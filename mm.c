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
 * if the block is allocated. The list has the following form:
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
 *
 * Segregated lists: partition the block sizes by powers of two 
 * starting from 3 blocks, because it's the minimum size requirement
 *
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

#define PUT_ADDR(p, val)    (*(int *)(p) = (int)(long)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, read address of its next/prev free block pointer */
#define NEXTP(bp)      ((int *)((char *)(bp)))
#define PREVP(bp)      ((int *)((char *)(bp) + WSIZE))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MIN_BLKSIZE 16

/* class no: 0 - NUM_FREELIST-1 */
#define NUM_FREELIST 10

/* The only global variable is a pointer to the first block */
char *heap_listp;

/* function prototypes for internal helper routines */
inline void *extend_heap(size_t words);
inline void place(void *bp, size_t asize);
inline void *find_fit(size_t asize);
inline void *coalesce(void *bp);
inline void printblock(void *bp);
inline void checkblock(void *bp);
inline void delete_freenode(void *bp);
inline void insert_freenode(void *bp);
inline void printfreelist();
inline void *getroot(int class);
inline int getclass(size_t size);
inline void check_heapboundaries(void *heapstart, void *heapend);
inline void checkfreelist(int freeblockcount);
inline int aligned(const void *p);
inline int in_heap(const void *p);
inline void *offset2addr(int offset);
inline void *next_free_blck(void *bp);
inline void *prev_free_blck(void *bp);

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
        return bp;
    }
    
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE/8);
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
inline void delete_freenode(void *bp)
{
    void *next_free_block_addr = next_free_blck(bp);
    void *prev_free_block_addr = (void *)prev_free_blck(bp);
    PUT_ADDR(NEXTP(prev_free_block_addr), next_free_block_addr);
    if (next_free_block_addr != NULL) {
        PUT_ADDR(PREVP(next_free_block_addr), prev_free_block_addr);
    }
}

/*
 * insert_freenode - insert the freed block to the free list
 */
inline void insert_freenode(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    void *root = getroot(getclass(size));
    void *nextp = next_free_blck(root);
    void *prevp = root;
    for (; nextp!=NULL && GET_SIZE(HDRP(nextp)) < size; prevp = nextp, nextp = (char *)next_free_blck(nextp)) {

    }

    PUT_ADDR(NEXTP(bp), nextp);
    PUT_ADDR(PREVP(bp), prevp);
    PUT_ADDR(NEXTP(prevp), bp);
    if (nextp != NULL) {
        PUT_ADDR(PREVP(nextp), bp);
    }
}


/*
 * realloc - you may want to look at mm-naive.c
 */
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
    
    oldsize = GET_SIZE(HDRP(oldptr));
    
    /* If size <= old size or the old block has a free block next to it,
       then just return the oldptr
     */
    size_t asize = MAX(ALIGN(size + SIZE_T_SIZE), MIN_BLKSIZE);
    // smaller than the old block
    if (asize <= oldsize) {
        place(oldptr, asize);
        return oldptr;
    }
    else {
        // enough space in next free block
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr)))) {
            size_t nsize = GET_SIZE(HDRP(NEXT_BLKP(oldptr))) + oldsize;
            
            if (nsize > asize) {
                delete_freenode(NEXT_BLKP(oldptr));
                PUT(HDRP(oldptr), PACK(nsize, 1));
                PUT(FTRP(oldptr), PACK(nsize,1));
                place(oldptr, asize);
                return oldptr;
            }
        }
    }
    
    newptr = malloc(size);
    
    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }
    
    /* Copy the old data. */
    
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
    if (verbose)
        printf("Check heap: \n");
    char *bp = heap_listp;
    int free_block_flag = 0;
    int free_block_count = 0;
    
    if (verbose)
        printf("Heap (%p):\n", heap_listp);
    
    // check prologue block
    if ((GET_SIZE(HDRP(heap_listp)) != OVERHEAD) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);
    
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printblock(bp);
        checkblock(bp);
        
        // check coalescing
        if (!GET_ALLOC(HDRP(bp))) {
            if (free_block_flag == 1) {
                printf("Error: consecutive free blocks %p | %p in the heap.\n", PREV_BLKP(bp),bp);
            }
            free_block_flag = 1;
            free_block_count++;
        } else {
            free_block_flag = 0;
        }
        
    }
    
    if (verbose)
        printblock(bp);
    
    // check epilogue block
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
    
    // print heap boundaries
    check_heapboundaries(heap_listp-DSIZE, bp-1);

    if (verbose) {
        printfreelist();
    }
    checkfreelist(free_block_count);
}


/* The remaining routines are internal helper routines */

/*
 * getclass - Get class for given size
 */
inline int getclass(size_t size)
{
    int block = size / DSIZE;

    if (block <= 4) {
        return 0;
    }
    if (block <= 8) {
        return 1;
    }
    if (block <= 16) {
        return 2;
    }
    if (block <= 32) {
        return 3;
    }
    if (block <= 64) {
        return 4;
    }
    if (block <= 128) {
        return 5;
    }
    if (block <= 256) {
        return 6;
    }
    if (block <= 512) {
        return 7;
    }
    if (block <= 1024) {
        return 8;
    }
    return 9;

}

/*
 * getroot - Get root node for corresponding class
 */
inline void *getroot(int class)
{
    return heap_listp + class * 2 * DSIZE;
}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
inline void *extend_heap(size_t words)
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
inline void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    int is_realloc = GET_ALLOC(HDRP(bp));
    
    if ((csize - asize) >= MIN_BLKSIZE) {

        if (!is_realloc) {
            delete_freenode(bp);
        }
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        dbg_printblock(bp);
        bp = NEXT_BLKP(bp);
        
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        
        dbg_printblock(bp);
        insert_freenode(bp);
        
        dbg_printblock(bp);
    }
    else {
        if (!is_realloc) {
            delete_freenode(bp);
        }
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        
    }
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
inline void *find_fit(size_t asize)
{
    dbg_printf("FINDING FIT: ");
    void *bp;
    int class = getclass(asize);
    for (int i = class; i < NUM_FREELIST; i++) {
        void *root = getroot(i);
        /* first fit search */
        for (bp = next_free_blck(root); bp != NULL; bp = next_free_blck(bp)) {
            dbg_printf(" %lx > ", (long)bp);
            if (asize <= GET_SIZE(HDRP(bp))) {
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
inline void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    dbg_printblock(bp);
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
        return(bp);
    }
    
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        delete_freenode(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        insert_freenode(PREV_BLKP(bp));
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
        return(PREV_BLKP(bp));
    }
}

/*
 * printblock - print the header, footer and pointers of each block
 */
inline void printblock(void *bp)
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
        next = (long)next_free_blck(bp);
        prev = (long)prev_free_blck(bp);
        printf("%p: header: [%d:%c] next: %lx prev: %lx footer: [%d:%c]\n", bp,
               (int)hsize, (halloc ? 'a' : 'f'), next, prev,
               (int)fsize, (falloc ? 'a' : 'f'));
    } else {
        printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
               (int)hsize, (halloc ? 'a' : 'f'),
               (int)fsize, (falloc ? 'a' : 'f'));
    }
}

/*
 * printfreelist - print each free list
 */
inline void printfreelist()
{
    
    for (int i = 0; i < NUM_FREELIST; i++) {
        printf("Free list %d: ", i);
        char *bp = getroot(i);
        for (; bp != NULL; bp = next_free_blck(bp)) {
            printf(" %lx -> ",(long)bp);
        }
        printf("END\n");
    }
    
}

/*
 * checkblock - check alignment, minmium size requirement,
                and consistency of header and footer
 */
inline void checkblock(void *bp)
{
    if (!aligned(bp))
        printf("Error: %p is not aligned\n", bp);
    if (((char *)bp >= (heap_listp+2*NUM_FREELIST*DSIZE)) && GET_SIZE(HDRP(bp)) < MIN_BLKSIZE) {
        printf("Error: %p is less than the minimum size requirement\n", bp);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/*
 * check_heapboundaries - check if heap boundaries matches head and end blocks
 */
inline void check_heapboundaries(void *heapstart, void *heapend)
{
    if (heapstart != mem_heap_lo()) {
        printf("Error: heap start point %p is not equaled to heap low boundary %p\n",
               heapstart, mem_heap_lo());
    }
    if (heapend != mem_heap_hi()) {
        printf("Error: heap end point %p is not equaled to heap high boundary %p\n",
               heapend, mem_heap_hi());
    }
}

/*
 * checkfreelist - check the free list
 */
inline void checkfreelist(int freeblockcount)
{
    int free_count = 0;
    for (int i = 0; i < NUM_FREELIST; i++) {
        char *bp = getroot(i);
        bp = next_free_blck(bp);
        for (; bp != NULL; bp = next_free_blck(bp),free_count++) {
            
            void *next_free_block_addr = (void *)next_free_blck(bp);
            void *prev_free_block_addr = (void *)prev_free_blck(bp);
            // check pointer consistency
            if ((next_free_block_addr != NULL) && ((long)prev_free_blck(next_free_block_addr) != (long)bp)) {
                printf("Error: pointers not consistent:\n");
                printblock(bp);
                printblock(next_free_block_addr);
            }
            // check pointers in heap boundaries
            if (!in_heap(next_free_block_addr) || !in_heap(prev_free_block_addr)) {
                printf("Error: pointers not in heap %p or %p\n",next_free_block_addr,prev_free_block_addr);
            }
            
            // check if block falls in the right size class
            if (getclass(GET_SIZE(HDRP(bp))) != i) {
                printf("Error: block not fall within bucket size range\n");
            }
            
        }
    }
    
    // check if free counts match
    if (free_count != freeblockcount) {
        printf("Error: free count not matched: %d vs %d\n",freeblockcount,free_count);
    }
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
inline int in_heap(const void *p) {
    if (p == NULL) {
        return 1;
    }
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
inline int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * offset2addr - restore the offset to address
 */
inline void *offset2addr(int offset)
{
    if (offset) {
        return (void *)((long)offset | 0x800000000);
    }
    else {
        return NULL;
    }
}
/*
 * next_free_blck - Given block bp, get next free block
 */
inline void *next_free_blck(void *bp)
{
    int offset = *NEXTP(bp);
    return offset2addr(offset);
}

/*
 * prev_free_blck - Given block bp, get previous block
 */
inline void *prev_free_blck(void *bp)
{
    int offset = *PREVP(bp);
    return offset2addr(offset);
}
