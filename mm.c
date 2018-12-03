/*
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first fit placement, and boundary tag coalescing, as described
 * in the CS:APP2e text. Blocks must be aligned to doubleword (8 byte)
 * boundaries. Minimum block size is 16 bytes.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your group information in the following struct.
 ********************************************************/
group_t group = {
        "79",

        "Zachary Hynes",
        "zamhynes2-c@my.cityu.edu.hk",

        "Jasper Spierling",
        "jspierlin2-c@my.cityu.edu.hk",

        "Christian Wanzek",
        "ckwanzek2-c@my.cityu.edu.hk"

        "",
        ""
};

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define POINTERSIZE       sizeof(void *)
#define MIN_SIZE    (2*DSIZE)

/*  HYNES: CHUNKSIZE = 4096 bytes, the minimum size a file must occupy is one block,
 * which is usually 4096 bytes/4K on most filesystems. */


#define MAX(x, y) ((x) > (y)? (x) : (y)) //HYNES: If x > y THEN x, IF NOT, then y.

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //HYNES: | is the bitwise OR

/* Read and write a word at address p */
/* HYNES: GET(p) first casts p into a unsigned integer pointer
 * (which means the value of p is an address that points to an unsigned int - 4 bytes)
 * and then it uses the * Dereferencing Operator to go to the address stored in p and access it. */
#define GET(p)       (*(unsigned int *)(p))

// get_next, get_previous added for free block expicit list pointers
#define GET_NEXT(bp) (*(unsigned long *)(bp))
#define GET_PREVIOUS(bp) (*(((unsigned long *)(bp))+1))


#define PUT(p, val)  (*(unsigned int *)(p) = (val))
#define PUT_POINTER(p, ptr) (*(unsigned long *)p =((unsigned long)(ptr)))

/* Read the size and allocated fields from address p */
/* HYNES: ~ is the bitwise COMPLIMENT (Negation)
 * WHATEVER IS AT P:                XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX (32 bits)
 *                                & 11111111111111111111111111111000 (32 bits)
                                ----------------------------------------------
                                    XXXXXXXXXXXXXXXXXXXXXXXXXXXXX000 (32 bits)
 */
#define GET_SIZE(p)  (GET(p) & ~0x7)

/* HYNES:
 * WHATEVER IS AT P:                XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX (32 bits)
 *                                & 00000000000000000000000000000001 (32 bits)
                                ----------------------------------------------
                                    0000000000000000000000000000000X (32 bits)
 */
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
/* Jasper: char pointer bc a char size is one byte, so adding one to the pointer moves it to next byte in memory,
 * whereas adding one to an int pointer would move it 4 bytes on since an int's size is 4 bytes */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static unsigned long **free_list_head = NULL; /* pointer to the beginning of explicit free list */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);

static void place(void *bp, size_t asize);

static void *find_fit(size_t asize);

static void *coalesce(void *bp);

static void printblock(void *bp);

static void checkheap(int verbose);

static void checkblock(void *bp);


// mm_init - Initialize the memory manager

int mm_init(void) {
    /* Create the initial empty heap */
    //HYNES: heap_listp is the pointer to the first block of the heap
    //HYNES: mem_sbrk is the last block of memory in the current heap

    //==============================
    //-------------PACK-------------
    //==============================
    //Jasper: DSIZE = 8, 8 in binary is 1000
    //Jasper: PACK(1000, 1) = 1000 | 0001 => 1001

    //==============================
    //-------------PUT-------------
    //==============================


    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */    //HYNES: 0   ???
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */      //HYNES: 1001
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */      //HYNES: 1001
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */      //HYNES: 0001
    heap_listp += (2 * WSIZE); //HYNES: create a buffer zone of 2 WORDS (8 bytes)???

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */



    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) //HYNES:  If it does not extend by an even number of words, it will return NULL.
        return -1;
    return 0; // HYNES: Returns 0 to main function if the heap was extended in an properly aligned manner


    //HYNES: An interesting visual I quote from "https://www.cs.cmu.edu/~fp/courses/15213-s05/code/18-malloc/malloc.c" for better understanding
    /*
     * Simple allocator based on implicit free lists with boundary
     * tag coalescing. Each block has header and footer of the form:
     *
     *      31                     3  2  1  0
     *      -----------------------------------
     *     | s  s  s  s  ... s  s  s  0  0  a/f
     *      -----------------------------------
     *
     * where s are the meaningful size bits and a/f is set
     * iff the block is allocated. The heap has the following form:
     *
     * begin                                                                    end
     * heap         | 4 bytes  | 4 bytes  |                       |  4 bytes |  heap
     *      -----------------------------------------------------------------
     *     |        | prologue | prologue |        0 or more      | epilogue |
     *     |  pad   | hdr(8:a) | ftr(8:a) |       user blocks     | hdr(8:a) |
     *      -----------------------------------------------------------------
     *     |        |       prologue      |  The blocks we store  | epilogue |
     *     |        |         block       |        go here        | block    |
     *
     * The allocated prologue and epilogue blocks are overhead that
     * eliminate edge conditions during coalescing.
     */
}


// mm_malloc - Allocate a block with at least size bytes of payload

void *mm_malloc(size_t size) {

    printf("Allocating block of size: %zu bytes\n", size);
    checkheap(1);

    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp; //HYNES: Block Pointer

    if (heap_listp == 0) {
        printf("Initializing the Heap...");
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) //HYNES: size <= 8 bytes
        asize = MIN_SIZE; //HYNES: asize = 16 bytes
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) /
                         DSIZE); //HYNES: asize = adjusted size to satisfy alignment requirement

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);

        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    //TODO Once we have the new memory, it gets placed as the head of the free list & is given a pointer to the old free list header

    place(bp, asize);

    return bp;
}


// mm_free - Free a block

void mm_free(void *bp) {
    printf("Freeing block: ");
    printblock(bp);
    if (bp == 0)
        return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0) {
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);


}


// coalesce - Boundary tag coalescing. Return ptr to coalesced block

static void add_to_free_list(unsigned long **free_block_pointer) {
    //set next pointer of new free block to current head of free list;
    if (free_list_head != NULL)
        PUT_POINTER(free_block_pointer, free_list_head);
    else
        *free_block_pointer = NULL;

    //set head of free list to new free block;
    free_list_head = free_block_pointer;
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {              /* Case 1 */
        add_to_free_list(bp);                   // Jasper, Hynes
        return bp;

    } else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

    } else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

    } else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // Once we have the new coalesced block, it gets placed as the head of the free list & is given a pointer to the old free list header

    add_to_free_list(bp);                       // Jasper, Hynes
    return bp;
}


// checkheap() - We don't check anything right now.

void mm_checkheap(int verbose) {
}


// The remaining routines are internal helper routines


// extend_heap - Extend heap with free block and return its block pointer

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */


    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= MIN_SIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        //Make sure the leftover free block gets placed as the head of the free list & is given a pointer to the old free list header (coalescce() is not called, therefore placement needed)

        add_to_free_list(bp);                    // Jasper, Hynes

    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }


}


// find_fit - Find a fit for a block with asize bytes

static void *find_fit(size_t asize) {
    /* First fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* No fit */

}

//TODO Write a new find_fit_explicit function that works with our free list

static void printblock(void *bp) {
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp,
           hsize, (halloc ? 'a' : 'f'),
           fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp) {
    if ((size_t) bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/*
 * checkheap - Minimal check of the heap for consistency
 */
void checkheap(int verbose) {
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", (void *) heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
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

//    //Check Heap Size
//    printf("\nThis is the heap size: %zu", (size_t)mem_heapsize());
//    printf("bytes.\n");


//    //Check value of the first byte of the heap
//    printf("FIRST Byte of the Heap:\n");
//    printf("This is the address of the first byte of the heap: %p\n", mem_heap_lo());
//    printf("This is the value of the first byte of the heap: %d", *((int*)mem_heap_lo())); //Typecast the mem_heap_lo into an integer pointer (int*), then add 1 int* to that memory address and dereference it
//    printf(" - (Expected: 0)\n\n");
////    printf("This is the first byte of the heap: %d\n", *(int*)(mem_heap_lo()+4)); //Get the memory byte address of mem_heap_lo and add 4 bytes to it, then type cast it to integer pointer (int*) and dereference it.
//
//
//    //Check value of the last byte of the heap
//    printf("LAST Byte of the Heap:\n");
//    printf("This is the address of the last byte of the heap: %p\n", mem_heap_hi());
//    printf("This is the value of the last byte of the heap: %d", *((int*)(mem_heap_hi()-3))); //Typecast the mem_heap_lo into an integer pointer (int*), then add 1 int* to that memory address and dereference it
//    printf(" - (Expected: 1)\n\n");

    //TODO Check if all free list pointers point between mem_heap_lo() and mem_heap_high()

    //Check each blocks header and footer:
    //Size -- Already implicitly implemented in static void checkblock(void *bp)
    //Essentially, if the checkBlock function returns a proper header and footer, then the size stored in the header is the correct size.
    //Get footer address
    //Get header address
    //HeaderAddress - FooterAddress = Size
    //Verify with size written in header & footer


    //Alignment -- Already implemented in static void checkblock(void *bp)
    //Previous
    //Next
    //Allocate Bit Consistency
    //Matching Header and Footer -- Already implemented in static void checkblock(void *bp)

}