/*
 *	This file is a part of Hierarchical Allocator library.
 *	Copyright (c) 2004-2011 Alex Pankratov. All rights reserved.
 *
 *	http://swapped.cc/halloc
 */

/*
 *	The program is distributed under terms of BSD license.
 *	You can obtain the copy of the license by visiting:
 *
 *	http://www.opensource.org/licenses/bsd-license.php
 */

#include <malloc.h>  /* realloc */
#include <string.h>  /* memset & co */
#include <stddef.h>  /* offsetof */
#include <assert.h>

#include "halloc.h"


/* align.h
   -------------------------------------------------------------------------- */

/*
 *	a type with the most strict alignment requirements
 */
union max_align
{
	char   c;
	short  s;
	long   l;
	int    i;
	float  f;
	double d;
	void * v;
	void (*q)(void);
};

typedef union max_align max_align_t;


/* macros.h
   -------------------------------------------------------------------------- */

/*
 	restore pointer to the structure by a pointer to its field
 */
#define structof(p,t,f) ((t*)(- offsetof(t,f) + (void*)(p)))

/*
 *	redefine for the target compiler
 */
#define static_inline static __inline__


/* hlist.h
   -------------------------------------------------------------------------- */

/*
 *	weak double-linked list w/ tail sentinel
 */
typedef struct hlist_head  hlist_head_t;
typedef struct hlist_item  hlist_item_t;

/*
 *
 */
struct hlist_head
{
	hlist_item_t * next;
};

struct hlist_item
{
	hlist_item_t * next;
	hlist_item_t ** prev;
};

/*
 *	shared tail sentinel
 */
struct hlist_item hlist_null;

static_inline void hlist_init(hlist_head_t * h);
static_inline void hlist_init_item(hlist_item_t * i);
static_inline void hlist_add(hlist_head_t * h, hlist_item_t * i);
static_inline void hlist_del(hlist_item_t * i);
static_inline void hlist_relink(hlist_item_t * i);
static_inline void hlist_relink_head(hlist_head_t * h);

#define hlist_for_each(i, h) \
	for (i = (h)->next; i != &hlist_null; i = i->next)

#define hlist_for_each_safe(i, tmp, h) \
	for (i = (h)->next, tmp = i->next; \
	     i!= &hlist_null; \
	     i = tmp, tmp = i->next)

/*
 *	static
 */
static_inline void hlist_init(hlist_head_t * h)
{
	assert(h);
	h->next = &hlist_null;
}

static_inline void hlist_init_item(hlist_item_t * i)
{
	assert(i);
	i->prev = &i->next;
	i->next = &hlist_null;
}

static_inline void hlist_add(hlist_head_t * h, hlist_item_t * i)
{
	hlist_item_t * next;
	assert(h && i);

	next = i->next = h->next;
	next->prev = &i->next;
	h->next = i;
	i->prev = &h->next;
}

static_inline void hlist_del(hlist_item_t * i)
{
	hlist_item_t * next;
	assert(i);

	next = i->next;
	next->prev = i->prev;
	*i->prev = next;

	hlist_init_item(i);
}

static_inline void hlist_relink(hlist_item_t * i)
{
	assert(i);
	*i->prev = i;
	i->next->prev = &i->next;
}

static_inline void hlist_relink_head(hlist_head_t * h)
{
	assert(h);
	h->next->prev = &h->next;
}


/* halloc.c
   -------------------------------------------------------------------------- */

/*
 *	block control header
 */
typedef struct hblock
{
#ifdef DEBUG
#define HH_MAGIC    0x20040518L
	long          magic;
#endif
	hlist_item_t  siblings; /* 2 pointers */
	hlist_head_t  children; /* 1 pointer  */
	max_align_t   data[1];  /* not allocated, see below */

} hblock_t;

#define sizeof_hblock offsetof(hblock_t, data)

/*
 *
 */
realloc_t halloc_allocator = NULL;

#define allocator halloc_allocator

/*
 *	static methods
 */
static void _set_allocator(void);
static void * _realloc(void * ptr, size_t n);

static int  _relate(hblock_t * b, hblock_t * p);
static void _free_children(hblock_t * p);

/*
 *	Core API
 */
void * halloc(void * ptr, size_t len)
{
	hblock_t * p;

	/* set up default allocator */
	if (! allocator)
	{
		_set_allocator();
		assert(allocator);
	}

	/* calloc */
	if (! ptr)
	{
		if (! len)
			return NULL;

		p = allocator(0, len + sizeof_hblock);
		if (! p)
			return NULL;
#ifdef DEBUG
		p->magic = HH_MAGIC;
#endif
		hlist_init(&p->children);
		hlist_init_item(&p->siblings);

		return p->data;
	}

	p = structof(ptr, hblock_t, data);
#ifdef DEBUG
	assert(p->magic == HH_MAGIC);
#endif

	/* realloc */
	if (len)
	{
		p = allocator(p, len + sizeof_hblock);
		if (! p)
			return NULL;

		hlist_relink(&p->siblings);
		hlist_relink_head(&p->children);

		return p->data;
	}

	/* free */
	_free_children(p);
	hlist_del(&p->siblings);
	allocator(p, 0);

	return NULL;
}

void hattach(void * block, void * parent)
{
	hblock_t * b, * p;

	if (! block)
	{
		assert(! parent);
		return;
	}

	/* detach */
	b = structof(block, hblock_t, data);
#ifdef DEBUG
	assert(b->magic == HH_MAGIC);
#endif

	hlist_del(&b->siblings);

	if (! parent)
		return;

	/* attach */
	p = structof(parent, hblock_t, data);
#ifdef DEBUG
	assert(p->magic == HH_MAGIC);
#endif

	/* sanity checks */
	assert(b != p);          /* trivial */
	assert(! _relate(p, b)); /* heavy ! */

	hlist_add(&p->children, &b->siblings);
}

/*
 *	malloc/free api
 */
void * h_malloc(size_t len)
{
	return halloc(0, len);
}

void * h_calloc(size_t n, size_t len)
{
	void * ptr = halloc(0, len*=n);
	return ptr ? memset(ptr, 0, len) : NULL;
}

void * h_realloc(void * ptr, size_t len)
{
	return halloc(ptr, len);
}

void   h_free(void * ptr)
{
	halloc(ptr, 0);
}

char * h_strdup(const char * str)
{
	size_t len = strlen(str);
	char * ptr = halloc(0, len + 1);
	return ptr ? (ptr[len] = 0, memcpy(ptr, str, len)) : NULL;
}

/*
 *	static stuff
 */
static void _set_allocator(void)
{
	void * p;
	assert(! allocator);

	/*
	 *	the purpose of the test below is to check the behaviour
	 *	of realloc(ptr, 0), which is defined in the standard
	 *	as an implementation-specific. if it returns zero,
	 *	then it's equivalent to free(). it can however return
	 *	non-zero, in which case it cannot be used for freeing
	 *	memory blocks and we'll need to supply our own version
	 *
	 *	Thanks to Stan Tobias for pointing this tricky part out.
	 */
	allocator = realloc;
	if (! (p = malloc(1)))
		/* hmm */
		return;

	if ((p = realloc(p, 0)))
	{
		/* realloc cannot be used as free() */
		allocator = _realloc;
		free(p);
	}
}

static void * _realloc(void * ptr, size_t n)
{
	/*
	 *	free'ing realloc()
	 */
	if (n)
		return realloc(ptr, n);
	free(ptr);
	return NULL;
}

static int _relate(hblock_t * b, hblock_t * p)
{
	hlist_item_t * i;

	if (!b || !p)
		return 0;

	/*
	 *  since there is no 'parent' pointer, which would've allowed
	 *  O(log(n)) upward traversal, the check must use O(n) downward
	 *  iteration of the entire hierarchy; and this can be VERY SLOW
	 */
	hlist_for_each(i, &p->children)
	{
		hblock_t * q = structof(i, hblock_t, siblings);
		if (q == b || _relate(b, q))
			return 1;
	}
	return 0;
}

static void _free_children(hblock_t * p)
{
	hlist_item_t * i, * tmp;

#ifdef DEBUG
	/*
	 *	this catches loops in hierarchy with almost zero
	 *	overhead (compared to _relate() running time)
	 */
	assert(p && p->magic == HH_MAGIC);
	p->magic = 0;
#endif
	hlist_for_each_safe(i, tmp, &p->children)
	{
		hblock_t * q = structof(i, hblock_t, siblings);
		_free_children(q);
		allocator(q, 0);
	}
}
