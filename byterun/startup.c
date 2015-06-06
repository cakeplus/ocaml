/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*         Xavier Leroy and Damien Doligez, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

/* Starting up and shutting down the runtime system */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>

#include "backtrace.h"
#include "callback.h"
#include "custom.h"
#include "debugger.h"
#include "fail.h"
#include "freelist.h"
#include "gc.h"
#include "gc_ctrl.h"
#include "instrtrace.h"
#include "intext.h"
#include "memory.h"
#include "misc.h"
#include "mlvalues.h"
#include "osdeps.h"
#include "printexc.h"
#include "startup.h"
#include "sys.h"
#include "finalise.h"

#ifdef NATIVE_CODE
#  include "stack.h"
#else
#  include "alloc.h"
#  include "config.h"
#  include "dynlink.h"
#  include "exec.h"
#  include "fix_code.h"
#  include "interp.h"
#  include "io.h"
#  include "minor_gc.h"
#  include "prims.h"
#  include "reverse.h"
#  include "signals.h"
#  include "stacks.h"
#  include "version.h"
#  ifdef HAS_UNISTD
#    include <unistd.h>
#  endif
#  ifdef _WIN32
#    include <process.h>
#  endif
#endif


/* Machine-dependent initialization of the floating-point hardware
   so that it behaves as much as possible as specified in IEEE */
extern void caml_init_ieee_floats (void);


/* PR 4887: avoid crash box of windows runtime on some system calls */
#ifdef _MSC_VER
extern void caml_install_invalid_parameter_handler();
#endif


/* Parameter: debugging support for ocamlyacc-generated parsers (parsing.c) */
extern int caml_parser_trace;


/* Configuration parameters and flags */
static uintnat percent_free_init = Percent_free_def;
static uintnat max_percent_free_init = Max_percent_free_def;
static uintnat minor_heap_init = Minor_heap_def;
static uintnat heap_chunk_init = Heap_chunk_def;
static uintnat heap_size_init = Init_heap_def;
static uintnat max_stack_init = Max_stack_def;


/* Statically allocated atoms */
CAMLexport header_t caml_atom_table[256];


/* The number of outstanding calls to caml_startup */
static int startup_count = 0;


/* The option letter for each runtime option is the first letter of the
   last word of the ML name of the option (see [stdlib/gc.mli]).
   Except for l (maximum stack size) and h (initial heap size).
*/
static void scanmult (char *opt, uintnat *var)
{
  char mult = ' ';
  unsigned int val;
  sscanf (opt, "=%u%c", &val, &mult);
  sscanf (opt, "=0x%x%c", &val, &mult);
  switch (mult) {
  case 'k':   *var = (uintnat) val * 1024; break;
  case 'M':   *var = (uintnat) val * 1024 * 1024; break;
  case 'G':   *var = (uintnat) val * 1024 * 1024 * 1024; break;
  default:    *var = (uintnat) val; break;
  }
}


/* Parse the OCAMLRUNPARAM variable */
static void parse_camlrunparam(void)
{
  char *opt = getenv ("OCAMLRUNPARAM");
  uintnat p;

  if (opt == NULL) opt = getenv ("CAMLRUNPARAM");

  if (opt != NULL){
    while (*opt != '\0'){
      switch (*opt++){
      case 'a': scanmult (opt, &p); caml_set_allocation_policy (p); break;
      case 'b': caml_record_backtrace(Val_true); break;
      case 'h': scanmult (opt, &heap_size_init); break;
      case 'i': scanmult (opt, &heap_chunk_init); break;
      case 'l': scanmult (opt, &max_stack_init); break;
      case 'o': scanmult (opt, &percent_free_init); break;
      case 'O': scanmult (opt, &max_percent_free_init); break;
      case 'p': caml_parser_trace = 1; break;
      /* case 'R': see stdlib/hashtbl.mli */
      case 's': scanmult (opt, &minor_heap_init); break;
#if defined(DEBUG) && !defined(NATIVE_CODE)
      case 't': caml_trace_flag = 1; break;
#endif
      case 'v': scanmult (opt, &caml_verb_gc); break;
      }
    }
  }
}


#ifndef NATIVE_CODE // Bytecode runtime
/* -------------------------------------------------------------------------- */

#ifndef O_BINARY
#define O_BINARY 0
#endif

#ifndef SEEK_END
#define SEEK_END 2
#endif

/* Initialize the atom table */

static void init_atoms(void)
{
  int i;
  for(i = 0; i < 256; i++) caml_atom_table[i] = Make_header(0, i, Caml_white);
  if (caml_page_table_add(In_static_data,
                          caml_atom_table, caml_atom_table + 256) != 0) {
    caml_fatal_error("Fatal error: not enough memory for initial page table");
  }
}

/* Read the trailer of a bytecode file */

static void fixup_endianness_trailer(uint32 * p)
{
#ifndef ARCH_BIG_ENDIAN
  Reverse_32(p, p);
#endif
}

static int read_trailer(int fd, struct exec_trailer *trail)
{
  if (lseek(fd, (long) -TRAILER_SIZE, SEEK_END) == -1)
    return BAD_BYTECODE;
  if (read(fd, (char *) trail, TRAILER_SIZE) < TRAILER_SIZE)
    return BAD_BYTECODE;
  fixup_endianness_trailer(&trail->num_sections);
  if (strncmp(trail->magic, EXEC_MAGIC, 12) == 0)
    return 0;
  else
    return BAD_BYTECODE;
}

int caml_attempt_open(char **name, struct exec_trailer *trail,
                      int do_open_script)
{
  char * truename;
  int fd;
  int err;
  char buf [2];

  truename = caml_search_exe_in_path(*name);
  *name = truename;
  caml_gc_message(0x100, "Opening bytecode executable %s\n",
                  (uintnat) truename);
  fd = open(truename, O_RDONLY | O_BINARY);
  if (fd == -1) {
    caml_gc_message(0x100, "Cannot open file\n", 0);
    return FILE_NOT_FOUND;
  }
  if (!do_open_script) {
    err = read (fd, buf, 2);
    if (err < 2 || (buf [0] == '#' && buf [1] == '!')) {
      close(fd);
      caml_gc_message(0x100, "Rejected #! script\n", 0);
      return BAD_BYTECODE;
    }
  }
  err = read_trailer(fd, trail);
  if (err != 0) {
    close(fd);
    caml_gc_message(0x100, "Not a bytecode executable\n", 0);
    return err;
  }
  return fd;
}

/* Read the section descriptors */

void caml_read_section_descriptors(int fd, struct exec_trailer *trail)
{
  int toc_size, i;

  toc_size = trail->num_sections * 8;
  trail->section = caml_stat_alloc(toc_size);
  lseek(fd, - (long) (TRAILER_SIZE + toc_size), SEEK_END);
  if (read(fd, (char *) trail->section, toc_size) != toc_size)
    caml_fatal_error("Fatal error: cannot read section table\n");
  /* Fixup endianness of lengths */
  for (i = 0; i < trail->num_sections; i++)
    fixup_endianness_trailer(&(trail->section[i].len));
}

/* Position fd at the beginning of the section having the given name.
   Return the length of the section data in bytes, or -1 if no section
   found with that name. */

int32 caml_seek_optional_section(int fd, struct exec_trailer *trail, char *name)
{
  long ofs;
  int i;

  ofs = TRAILER_SIZE + trail->num_sections * 8;
  for (i = trail->num_sections - 1; i >= 0; i--) {
    ofs += trail->section[i].len;
    if (strncmp(trail->section[i].name, name, 4) == 0) {
      lseek(fd, -ofs, SEEK_END);
      return trail->section[i].len;
    }
  }
  return -1;
}

/* Position fd at the beginning of the section having the given name.
   Return the length of the section data in bytes. */

int32 caml_seek_section(int fd, struct exec_trailer *trail, char *name)
{
  int32 len = caml_seek_optional_section(fd, trail, name);
  if (len == -1)
    caml_fatal_error_arg("Fatal_error: section `%s' is missing\n", name);
  return len;
}

/* Read and return the contents of the section having the given name.
   Add a terminating 0.  Return NULL if no such section. */

static char * read_section(int fd, struct exec_trailer *trail, char *name)
{
  int32 len;
  char * data;

  len = caml_seek_optional_section(fd, trail, name);
  if (len == -1) return NULL;
  data = caml_stat_alloc(len + 1);
  if (read(fd, data, len) != len)
    caml_fatal_error_arg("Fatal error: error reading section %s\n", name);
  data[len] = 0;
  return data;
}

/* Invocation of ocamlrun: 4 cases.

   1.  runtime + bytecode
       user types:  ocamlrun [options] bytecode args...
       arguments:  ocamlrun [options] bytecode args...

   2.  bytecode script
       user types:  bytecode args...
   2a  (kernel 1) arguments:  ocamlrun ./bytecode args...
   2b  (kernel 2) arguments:  bytecode bytecode args...

   3.  concatenated runtime and bytecode
       user types:  composite args...
       arguments:  composite args...

Algorithm:
  1-  If argument 0 is a valid byte-code file that does not start with #!,
      then we are in case 3 and we pass the same command line to the
      OCaml program.
  2-  In all other cases, we parse the command line as:
        (whatever) [options] bytecode args...
      and we strip "(whatever) [options]" from the command line.

*/

/* Parse options on the command line */

static int parse_command_line(char **argv)
{
  int i, j;

  for(i = 1; argv[i] != NULL && argv[i][0] == '-'; i++) {
    switch(argv[i][1]) {
#ifdef DEBUG
    case 't':
      caml_trace_flag++;
      break;
#endif
    case 'v':
      if (!strcmp (argv[i], "-version")){
        printf ("The OCaml runtime, version " OCAML_VERSION "\n");
        exit (0);
      }else if (!strcmp (argv[i], "-vnum")){
        printf (OCAML_VERSION "\n");
        exit (0);
      }else{
        caml_verb_gc = 0x001+0x004+0x008+0x010+0x020;
      }
      break;
    case 'p':
      for (j = 0; caml_names_of_builtin_cprim[j] != NULL; j++)
        printf("%s\n", caml_names_of_builtin_cprim[j]);
      exit(0);
      break;
    case 'b':
      caml_record_backtrace(Val_true);
      break;
    case 'I':
      if (argv[i + 1] != NULL) {
        caml_ext_table_add(&caml_shared_libs_path, argv[i + 1]);
        i++;
      }
      break;
    default:
      caml_fatal_error_arg("Unknown option %s.\n", argv[i]);
    }
  }
  return i;
}


#ifdef _WIN32
extern void caml_signal_thread(void * lpParam);
#endif

/* Main entry point when loading code from a file */

CAMLexport void caml_main(char **argv)
{
  int fd, pos;
  struct exec_trailer trail;
  struct channel * chan;
  value res;
  char * shared_lib_path, * shared_libs, * req_prims;
  char * exe_name;
  static char proc_self_exe[256];

  caml_stat_create_pool();
  caml_init_ieee_floats();
#ifdef _MSC_VER
  caml_install_invalid_parameter_handler();
#endif
  caml_init_custom_operations();
  caml_ext_table_init(&caml_shared_libs_path, 8);
  caml_external_raise = NULL;
  /* Determine options and position of bytecode file */
#ifdef DEBUG
  caml_verb_gc = 0xBF;
#endif
  parse_camlrunparam();
  pos = 0;

  /* First, try argv[0] (when ocamlrun is called by a bytecode program) */
  exe_name = argv[0];
  fd = caml_attempt_open(&exe_name, &trail, 0);

  /* Should we really do that at all?  The current executable is ocamlrun
     itself, it's never a bytecode program. */
  if (fd < 0
      && caml_executable_name(proc_self_exe, sizeof(proc_self_exe)) == 0) {
    exe_name = proc_self_exe;
    fd = caml_attempt_open(&exe_name, &trail, 0);
  }

  if (fd < 0) {
    pos = parse_command_line(argv);
    if (argv[pos] == 0)
      caml_fatal_error("No bytecode file specified.\n");
    exe_name = argv[pos];
    fd = caml_attempt_open(&exe_name, &trail, 1);
    switch(fd) {
    case FILE_NOT_FOUND:
      caml_fatal_error_arg("Fatal error: cannot find file '%s'\n", argv[pos]);
      break;
    case BAD_BYTECODE:
      caml_fatal_error_arg(
        "Fatal error: the file '%s' is not a bytecode executable file\n",
        exe_name);
      break;
    }
  }
  /* Read the table of contents (section descriptors) */
  caml_read_section_descriptors(fd, &trail);
  /* Initialize the abstract machine */
  caml_init_gc (minor_heap_init, heap_size_init, heap_chunk_init,
                percent_free_init, max_percent_free_init);
  caml_init_stack (max_stack_init);
  init_atoms();
  /* Initialize the interpreter */
  caml_interprete(NULL, 0);
  /* Initialize the debugger, if needed */
  caml_debugger_init();
  /* Load the code */
  caml_code_size = caml_seek_section(fd, &trail, "CODE");
  caml_load_code(fd, caml_code_size);
  /* Build the table of primitives */
  shared_lib_path = read_section(fd, &trail, "DLPT");
  shared_libs = read_section(fd, &trail, "DLLS");
  req_prims = read_section(fd, &trail, "PRIM");
  if (req_prims == NULL) caml_fatal_error("Fatal error: no PRIM section\n");
  caml_build_primitive_table(shared_lib_path, shared_libs, req_prims);
  caml_stat_free(shared_lib_path);
  caml_stat_free(shared_libs);
  caml_stat_free(req_prims);
  /* Load the globals */
  caml_seek_section(fd, &trail, "DATA");
  chan = caml_open_descriptor_in(fd);
  caml_global_data = caml_input_val(chan);
  caml_close_channel(chan); /* this also closes fd */
  caml_stat_free(trail.section);
  /* Ensure that the globals are in the major heap. */
  caml_oldify_one (caml_global_data, &caml_global_data);
  caml_oldify_mopup ();
  /* Initialize system libraries */
  caml_sys_init(exe_name, argv + pos);
#ifdef _WIN32
  /* Start a thread to handle signals */
  if (getenv("CAMLSIGPIPE"))
    _beginthread(caml_signal_thread, 4096, NULL);
#endif
  /* Execute the program */
  caml_debugger(PROGRAM_START);
  res = caml_interprete(caml_start_code, caml_code_size);
  if (Is_exception_result(res)) {
    caml_exn_bucket = Extract_exception(res);
    if (caml_debugger_in_use) {
      caml_extern_sp = &caml_exn_bucket; /* The debugger needs the
                                            exception value.*/
      caml_debugger(UNCAUGHT_EXC);
    }
    caml_fatal_uncaught_exception(caml_exn_bucket);
  }
  caml_shutdown();
}

/* Main entry point when code is linked in as initialized data */

CAMLexport void caml_startup_code(
           code_t code, asize_t code_size,
           char *data, asize_t data_size,
           char *section_table, asize_t section_table_size,
           char **argv)
{
  value res;
  char * cds_file;
  char * exe_name;
  static char proc_self_exe[256];

  // Second and subsequent calls are ignored,
  // since the runtime has already started
  startup_count++;
  if (startup_count > 1)
    return;

  caml_stat_create_pool();
  caml_init_ieee_floats();
#ifdef _MSC_VER
  caml_install_invalid_parameter_handler();
#endif
  caml_init_custom_operations();
#ifdef DEBUG
  caml_verb_gc = 63;
#endif
  cds_file = getenv("CAML_DEBUG_FILE");
  if (cds_file != NULL) {
    caml_cds_file = caml_strdup(cds_file);
  }
  parse_camlrunparam();
  exe_name = argv[0];
  if (caml_executable_name(proc_self_exe, sizeof(proc_self_exe)) == 0)
    exe_name = proc_self_exe;
  caml_external_raise = NULL;
  /* Initialize the abstract machine */
  caml_init_gc (minor_heap_init, heap_size_init, heap_chunk_init,
                percent_free_init, max_percent_free_init);
  caml_init_stack (max_stack_init);
  init_atoms();
  /* Initialize the interpreter */
  caml_interprete(NULL, 0);
  /* Initialize the debugger, if needed */
  caml_debugger_init();
  /* Load the code */
  caml_start_code = code;
  caml_code_size = code_size;
  caml_init_code_fragments();
  if (caml_debugger_in_use) {
    int len, i;
    len = code_size / sizeof(opcode_t);
    caml_saved_code = (unsigned char *) caml_stat_alloc(len);
    for (i = 0; i < len; i++) caml_saved_code[i] = caml_start_code[i];
  }
#ifdef THREADED_CODE
  caml_thread_code(caml_start_code, code_size);
#endif
  /* Use the builtin table of primitives */
  caml_build_primitive_table_builtin();
  /* Load the globals */
  caml_global_data = caml_input_value_from_block(data, data_size);
  /* Ensure that the globals are in the major heap. */
  caml_oldify_one (caml_global_data, &caml_global_data);
  caml_oldify_mopup ();
  /* Record the sections (for caml_get_section_table in meta.c) */
  caml_section_table = section_table;
  caml_section_table_size = section_table_size;
  /* Initialize system libraries */
  caml_sys_init(exe_name, argv);
  /* Execute the program */
  caml_debugger(PROGRAM_START);
  res = caml_interprete(caml_start_code, caml_code_size);
  if (Is_exception_result(res)) {
    caml_exn_bucket = Extract_exception(res);
    if (caml_debugger_in_use) {
      caml_extern_sp = &caml_exn_bucket; /* The debugger needs the
                                            exception value.*/
      caml_debugger(UNCAUGHT_EXC);
    }
    caml_fatal_uncaught_exception(caml_exn_bucket);
  }
}


#else // Native code runtime
/* -------------------------------------------------------------------------- */

char * caml_code_area_start, * caml_code_area_end;

/* Initialize the atom table and the static data and code area limits. */

struct segment { char * begin; char * end; };

static void init_atoms(void)
{
  extern struct segment caml_data_segments[], caml_code_segments[];
  int i;
  struct code_fragment * cf;

  for (i = 0; i < 256; i++) {
    caml_atom_table[i] = Make_header(0, i, Caml_white);
  }
  if (caml_page_table_add(In_static_data,
                          caml_atom_table, caml_atom_table + 256) != 0)
    caml_fatal_error("Fatal error: not enough memory for initial page table");

  for (i = 0; caml_data_segments[i].begin != 0; i++) {
    /* PR#5509: we must include the zero word at end of data segment,
       because pointers equal to caml_data_segments[i].end are static data. */
    if (caml_page_table_add(In_static_data,
                            caml_data_segments[i].begin,
                            caml_data_segments[i].end + sizeof(value)) != 0)
      caml_fatal_error("Fatal error: not enough memory for initial page table");
  }

  caml_code_area_start = caml_code_segments[0].begin;
  caml_code_area_end = caml_code_segments[0].end;
  for (i = 1; caml_code_segments[i].begin != 0; i++) {
    if (caml_code_segments[i].begin < caml_code_area_start)
      caml_code_area_start = caml_code_segments[i].begin;
    if (caml_code_segments[i].end > caml_code_area_end)
      caml_code_area_end = caml_code_segments[i].end;
  }
  /* Register the code in the table of code fragments */
  cf = caml_stat_alloc(sizeof(struct code_fragment));
  cf->code_start = caml_code_area_start;
  cf->code_end = caml_code_area_end;
  cf->digest_computed = 0;
  caml_ext_table_init(&caml_code_fragments_table, 8);
  caml_ext_table_add(&caml_code_fragments_table, cf);
}

/* These are termination hooks used by the systhreads library */
struct longjmp_buffer caml_termination_jmpbuf;
void (*caml_termination_hook)(void *) = NULL;

extern value caml_start_program (void);
extern void caml_init_signals (void);


void caml_main(char **argv)
{
  char * exe_name;
  static char proc_self_exe[256];
  value res;
  char tos;

  caml_stat_create_pool();
  caml_init_ieee_floats();
#ifdef _MSC_VER
  caml_install_invalid_parameter_handler();
#endif
  caml_init_custom_operations();
#ifdef DEBUG
  caml_verb_gc = 63;
#endif
  caml_top_of_stack = &tos;
  parse_camlrunparam();
  caml_init_gc (minor_heap_init, heap_size_init, heap_chunk_init,
                percent_free_init, max_percent_free_init);
  init_atoms();
  caml_init_signals();
  caml_debugger_init (); /* force debugger.o stub to be linked */
  exe_name = argv[0];
  if (exe_name == NULL) exe_name = "";
  if (caml_executable_name(proc_self_exe, sizeof(proc_self_exe)) == 0)
    exe_name = proc_self_exe;
  else
    exe_name = caml_search_exe_in_path(exe_name);
  caml_sys_init(exe_name, argv);
  if (sigsetjmp(caml_termination_jmpbuf.buf, 0)) {
    if (caml_termination_hook != NULL) caml_termination_hook(NULL);
    return;
  }
  res = caml_start_program();
  if (Is_exception_result(res))
    caml_fatal_uncaught_exception(Extract_exception(res));
  caml_shutdown();
}


void caml_startup(char **argv)
{
  // Second and subsequent calls are ignored,
  // since the runtime has already started
  startup_count++;
  if (startup_count > 1)
    return;

  caml_main(argv);
}

#endif // NATIVE_CODE
/* -------------------------------------------------------------------------- */


CAMLexport void caml_shutdown(void)
{
  if (startup_count <= 0)
    caml_fatal_error("Fatal error: a call to caml_shutdown has no "
                     "corresponding call to caml_startup");

  // Do nothing unless it's the last call remaining
  startup_count--;
  if (startup_count > 0)
    return;

  // Finalising values registered with Gc.finalise
  caml_empty_minor_heap();
  caml_finish_major_cycle();
  caml_final_do_all_calls();

  caml_finalise_heap();
#ifndef NATIVE_CODE
  caml_free_shared_libs();
#endif
  caml_stat_destroy_pool();
}
