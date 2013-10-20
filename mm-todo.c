/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

typedef struct header {
    struct header *next;
    size_t size;
} Header;

Header base;
Header *freelist = NULL;

static Header *morecore(size_t req_size);

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    Header *p, *prevp;
    size_t nunits;
    
    /* Alighment Header(8byte)   */
    /* 9 -> 9 + 7 -> 16 / 8 -> 2 + 1 -> 3 = nunits */
    nunits = ((size + sizeof(Header)-1) / sizeof(Header)) + 1;
    
    if ((prevp = freelist) == NULL) {
        /* base.next == base(.next) == base */
        base.next = freelist = prevp = &base;
        base.size = 0;
    }
    
    for (p = prevp->next; ;prevp = p, p = p->next) {
        if (p->size >= nunits) {
            if (p->size == nunits) {
                /* | |prevp...|    |p ..........|  |p->next ....|  |*/
                prevp->next = p->next;
            }
            else {
                /* | |prevp...|    |p ..|to user|  |p->next ....|  |*/
                p->size -= nunits;
                p = p + p->size;
                p->size = nunits;
            }
            freelist = prevp; /* TODO */
            return (void *)(p+1);
        }
        if (p == freelist) {
            if((p = morecore(nunits)) == NULL)
                return NULL;
        }
    }
}


/*
 * free
 */
void free (void *ptr) {
    if(!ptr) return;
    
    Header *target, *hit;
    
    target = ((Header *)ptr)-1;
    /* | |(target....)| |hit->next...|  ...   |hit.....| |*/
    /* hit = base(0xXXXXX)->next = base */
    /* base(0xXXXXX) < target || target > base(0xXXXX) */
    for (hit = freelist; !(hit < target && target < hit->next); hit = hit->next)
        if (hit >= hit->next && (hit < target || target < hit->next ))
            break;
    
    /* | |hit.....| |target.............| |hit->next->next....||*/
    if (target + target->size == hit->next) {
        target->size += hit->next->size;
        target->next = hit->next->next;
    }
    else {
        /* | |hit.....| |target.....|  |hit->next...| |hit->next->next....||*/
        target->next = hit->next;
    }
    
    /* | |hit......................| |hit->next->next....||*/
    if (hit + hit->size == target) {
        hit->size += target->size;
        hit->next = target->next;
    }
    else {
        /* | |hit.....| |target.....|  |hit->next...| |hit->next->next....||*/
        hit->next = target;
    }
    freelist = hit; /* TODO */
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;
    
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }
    
    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }
    
    newptr = malloc(size);
    
    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }
    
    /* Copy the old data. */
    oldsize = *SIZE_PTR(oldptr);
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);
    
    /* Free the old block. */
    free(oldptr);
    
    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;
    
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    
    return newptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {

    if (verbose)
        printf("Heap (%p):\n", freelist);
    
    in_heap(freelist);
    aligned(freelist);
}

/* extend heap */
static Header *morecore(size_t req_size)
{
    Header *extended_ptr;
    
    if (req_size < 1024)
        req_size = 1024;
    extended_ptr = (Header *)mem_sbrk(req_size * sizeof(Header));
    if (extended_ptr == (Header *)-1)
        return NULL;
    extended_ptr->size = req_size;
    free((void *)(extended_ptr+1));
    return freelist;
}
