/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*          Damien Doligez, projet Moscova, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 2000 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

#ifndef CAML_FINALISE_H
#define CAML_FINALISE_H

#include "roots.h"

void caml_final_update (void);
void caml_final_do_calls (void);
void caml_final_do_strong_roots (scanning_action f);
void caml_final_do_weak_roots (scanning_action f);
void caml_final_do_young_roots (scanning_action f);
void caml_final_empty_young (void);
value caml_final_register (value f, value v);

/* Forces finalisation of all values registered with caml_final_register,
   disregarding both local and global roots. GC must be in Phase_idle state.

   Value finalisation is performed in the reverse order to the
   corresponding calls to Gc.finalise (caml_final_register)

   Warning: if any of the finalisers themselves allocate finalisable objects,
   these objects will not be freed as part of the procedure.
*/
void caml_final_do_all_calls (void);

#endif /* CAML_FINALISE_H */
