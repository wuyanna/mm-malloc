/*
 * mm.c
 *
 * Simple allocator based on implicit free lists with boundary
 * tag coalescing. Each block has header and footer of the form:
 *
 *      31                     3  2  1  0
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      -----------------------------------
 *
 * where s are the meaningful size bits and a/f is set
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap
 *  -----------------------------------------------------------------
 * |  pad   | | | | | | | | | | | | zero or more usr blks | hdr(0:a) |
 *  -----------------------------------------------------------------
 *          |       seglist       |                       | epilogue |
 *          |        roots        |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
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

#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
# define dbg_printblock(a) printblock(a)
#else
# define dbg_printf(...)
# define dbg_printblock(a)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */


/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    16      /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

#define PUT_ADDR(p, val)    (*(long *)(p) = (long)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, read address of its next/prev free block pointer */
#define NEXTP(bp)      (long *)((char *)(bp))
#define PREVP(bp)      (long *)((char *)(bp) + DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

#define MIN_BLKSIZE 24

/* class no: 0 - NUM_FREELIST-1 */
#define NUM_FREELIST 10

/* The only global variable is a pointer to the first block */
static char *heap_listp;

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);
static void delete_freenode(void *bp);
static void insert_freenode(void *bp);
static void printfreelist();
static void *getroot(int class);
static int getclass(size_t size);
static int getrangeforclass(int class);
/*
 * mm_init - Initialize the memory manager
 * segregated list - save each root at beginning, each root is 2*DSIZE
 */
int mm_init(void)
{
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(DSIZE+NUM_FREELIST*DSIZE*2)) == NULL)
        return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    
    PUT(heap_listp+2*NUM_FREELIST*DSIZE+WSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;
    
    for (int i = 0; i < NUM_FREELIST; i++) {
        char *root = getroot(i);
        PUT(root-WSIZE, PACK(OVERHEAD, 1));  /* prologue header */
        PUT_ADDR(root, NULL);            /* root next free node */
        PUT(root+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */
    }
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
void *malloc(size_t size)
{
    dbg_printf("Calling mm_malloc........");
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;
    
    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    asize = MAX(ALIGN(size + SIZE_T_SIZE), MIN_BLKSIZE);
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        dbg_printf("place succeed: ");
        dbg_printblock(bp);
        dbg_printblock(NEXT_BLKP(bp));
        return bp;
    }
    
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Free a block
 */
void free(void *bp)
{
    dbg_printf("Calling mm_free........");
    if(!bp) return;
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * delete_freenode - delete the block from free list when it is allocated
 */
static void delete_freenode(void *bp)
{
    void *next_free_block_addr = (void *)*NEXTP(bp);
    void *prev_free_block_addr = (void *)*PREVP(bp);
    PUT_ADDR(NEXTP(prev_free_block_addr), next_free_block_addr);
    if (next_free_block_addr != NULL) {
        PUT_ADDR(PREVP(next_free_block_addr), prev_free_block_addr);
    }
    
}

/*
 * insert_freenode - insert the freed block to the free list
 */
static void insert_freenode(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    void *root = getroot(getclass(size));
    void *next_free_block_addr = (void *)*NEXTP(root);
    PUT_ADDR(NEXTP(bp), *NEXTP(root));
    PUT_ADDR(PREVP(bp), root);
    
    PUT_ADDR(NEXTP(root), bp);
    if (next_free_block_addr != NULL) {
        PUT_ADDR(PREVP(next_free_block_addr), bp);
    }
}


/* Not implemented. For consistency with 15-213 malloc driver */
void *realloc(void *oldptr, size_t size)
{
    dbg_printf("Calling mm_relloc........");
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
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose)
{
    char *bp = heap_listp;
    
    if (verbose)
        printf("Heap (%p):\n", heap_listp);
    
    if ((GET_SIZE(HDRP(heap_listp)) != OVERHEAD) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);
    
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printblock(bp);
        checkblock(bp);
    }
    
    if (verbose)
        printblock(bp);
    
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
    
    printfreelist();
}


/* The remaining routines are internal helper routines */

/*
 * getclass - Get class for given size
 */
static int getclass(size_t size)
{
    int block = size / DSIZE;
    for (int i = 0; i < NUM_FREELIST - 1; i++) {
        if (block <= getrangeforclass(i) && block > getrangeforclass(i-1)) {
            return i;
        }
    }
    return NUM_FREELIST-1;
}

static int getrangeforclass(int class)
{
    return 1 << (class + 2);
}

/*
 * getroot - Get root node for corresponding class
 */
static void *getroot(int class)
{
    return heap_listp + class * 2 * DSIZE;
}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;
	
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *) -1)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= MIN_BLKSIZE) {

        dbg_printf("SPLITTING: ");
        dbg_printblock(bp);
        dbg_printf("SPLITTED: ");
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        delete_freenode(bp);
        dbg_printblock(bp);
        bp = NEXT_BLKP(bp);
        
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        
        dbg_printblock(bp);
        insert_freenode(bp);
        
        dbg_printblock(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        delete_freenode(bp);
    }
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize)
{
    dbg_printf("FINDING FIT: ");
    void *bp;
    int class = getclass(asize);
    for (int i = class; i < NUM_FREELIST; i++) {
        void *root = getroot(i);
        /* first fit search */
        for (bp = root; bp != NULL; bp = (char *)*NEXTP(bp)) {
            dbg_printf(" %lx > ", (long)bp);
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                dbg_printf("FOUND!\n");
                return bp;
            }
        }
    }
    
    dbg_printf("NOT FOUND :(\n");
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    dbg_printf("Coalescing\n");
    dbg_printblock(PREV_BLKP(bp));
    dbg_printblock(NEXT_BLKP(bp));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        insert_freenode(bp);                  /* insert the free node to the head of freelist */
        return bp;
    }
    
    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_freenode(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        insert_freenode(bp);
        dbg_printblock(bp);
        return(bp);
    }
    
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        delete_freenode(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        insert_freenode(PREV_BLKP(bp));
        dbg_printblock(PREV_BLKP(bp));
        return(PREV_BLKP(bp));
    }
    
    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
        delete_freenode(PREV_BLKP(bp));
        delete_freenode(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        insert_freenode(PREV_BLKP(bp));
        dbg_printblock(PREV_BLKP(bp));
        return(PREV_BLKP(bp));
    }
}

static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;
    long next, prev;
    
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));
    
    
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }
    
    if (!halloc || (char *)bp < (heap_listp+2*NUM_FREELIST*DSIZE)) {
        next = *NEXTP(bp);
        prev = *PREVP(bp);
        printf("%p: header: [%d:%c] next: %lx prev: %lx footer: [%d:%c]\n", bp,
               (int)hsize, (halloc ? 'a' : 'f'), next, prev,
               (int)fsize, (falloc ? 'a' : 'f'));
    } else {
        printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
               (int)hsize, (halloc ? 'a' : 'f'),
               (int)fsize, (falloc ? 'a' : 'f'));
    }

    
}

static void printfreelist()
{
    
    for (int i = 0; i < NUM_FREELIST; i++) {
        printf("Free list %d: ", i);
        char *bp = getroot(i);
        for (; bp != NULL; bp = (char *)*NEXTP(bp)) {
            printf(" %lx -> ",(long)bp);
        }
        printf("END\n");
    }
    
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

