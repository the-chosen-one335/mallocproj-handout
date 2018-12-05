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
        /* Project group number (You're required to join a group on Canvas) */
        "79",
        /* First member's full name */
        "Zachary Hynes",
        /* First member's email address */
        "zamhynes2-c@my.cityu.edu.hk",
        /* Second member's full name (leave blank if none) */
        "Jasper Spierling",
        /* Second member's email address (leave blank if none) */
        "jspierlin2-c@my.cityu.edu.hk",
        /* Third member's full name (leave blank if none) */
        "Christian Wanzek",
        /* Third member's email address (leave blank if none) */
        "ckwanzek2-c@my.cityu.edu.hk"
        /* Fourth member's full name (leave blank if none) */
        "",
        /* Fourth member's email address (leave blank if none) */
        ""
};

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define POINTERSIZE       sizeof(void *)
#define MIN_SIZE    (3*DSIZE) //3 bc one for head/foot, one for 8byte next pointer, one for same size previous pointer
#define SIZE_OF_SEG_STORAGE   (number_of_lists*POINTERSIZE)
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


// go_bext, go_previous, get_next, get_previous added for free block expicit list pointers
#define GO_NEXT(bp) ((unsigned long **)(bp))
#define GO_PREVIOUS(bp) ((((unsigned long **)(bp))+1))

#define GET_NEXT(bp)     *GO_NEXT(bp)
#define GET_PREVIOUS(bp) *GO_PREVIOUS(bp)

//SEGMENTED: moves from heaplistp position AFTER mm_init back up to get to the pointers; setoff = 0 brings us to pointer closest to prologue, with every increment of setoff we move closer to the beginning of the heap
#define GO_LIST(offset) (((unsigned long **)(((char *)seg_list_head)+(POINTERSIZE*(offset)))))
#define GET_LIST(offset) *(GO_LIST(offset))


#define PUT(p, val)  (*(unsigned int *)(p) = (val))
#define PUT_POINTER(bp, next) (*(unsigned long *)(bp) =((unsigned long)(next)))

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
static void **seg_list_head = NULL;

//JASPER: NEW: number of lists located ON HEAP, set up in mm_init
static int number_of_lists = 1;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);

static void place(void *bp, size_t asize);

static void *find_fit(size_t asize);

static void *coalesce(void *bp);

static void printblock(void *bp);

static void checkheap(int verbose);

static void checkblock(void *bp);

static void remove_block_from_list(unsigned long *bp);

static void check_free_list();

static void *find_fit_segmented(size_t asize);

static int which_list(void* bp);

static int which_list_asize(int size);

// mm_init - Initialize the memory manager

int mm_init(void) {
    free_list_head = NULL;
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

//adjust for umber of pointers; old size: 4*WSIZE; one pointer: plus DSIZE
//reserves space between heap header (0,0) and prologue (8,1) for the pointers to lists
    if ((heap_listp = mem_sbrk(4 * WSIZE+SIZE_OF_SEG_STORAGE)) == (void *) -1)
        return -1;
    PUT(heap_listp, 0);/* Alignment padding */    //HYNES: 0   ???
    seg_list_head = heap_listp + (1 * WSIZE);
    //TODO: null the memory space reserved for pointers
    for(int i = 0; i<number_of_lists; i++){
        printf("GET CALLED THE FIRST TIME");
        GET_LIST(i)=NULL;
    }
    PUT(heap_listp + (1 * WSIZE+SIZE_OF_SEG_STORAGE), PACK(DSIZE, 1)); /* Prologue header */      //HYNES: 1001
    PUT(heap_listp + (2 * WSIZE+SIZE_OF_SEG_STORAGE), PACK(DSIZE, 1)); /* Prologue footer */      //HYNES: 1001
    PUT(heap_listp + (3 * WSIZE+SIZE_OF_SEG_STORAGE), PACK(0, 1));     /* Epilogue header */      //HYNES: 0001
    heap_listp += (2 * WSIZE+SIZE_OF_SEG_STORAGE); //HYNES: create a buffer zone of 2 WORDS (8 bytes)???

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

    //printf("Allocating block of size: %zu bytes\n", size);
    //checkheap(1);

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
    if ((bp = find_fit_segmented(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);

    return bp;
}


// mm_free - Free a block

void mm_free(void *bp) {
   // printf("Freeing block: ");
   // printblock(bp);
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

static void print_segmented(){
    //TODO: to test implementation, add a get_list call for locations to see what is found there
    printf("\nseg_list_head:\t\t\t%p\n", seg_list_head);
    printf("check (expected: ???):\t%zu\n", (size_t) *seg_list_head);
    printf("one word above seg_list_head (expected: 0): %d\n", *(unsigned int *)(((char *)seg_list_head)-WSIZE));
    printf("SIZE_OF_SEG_STORAGE:\t%zu\n", SIZE_OF_SEG_STORAGE);
    printf("heap_listp:\t\t\t\t%p\n", (void *)heap_listp);
    printf("check (expected: 9):\t%d\n\n", *heap_listp);


    int i = 0;
    for(i = 0; i<=number_of_lists; i++){
        printf("seg_list_head with offset %d: %p\n",i, GO_LIST(i));
        printf("\t\tvalue found at %d: %p\n",i, GET_LIST(i));

    }

    printf("\n");
}

static void remove_block_from_list(unsigned long *bp) {
    print_segmented();

    int num = which_list(bp);
    //printf("\nBeginning of remove_block: %p\n", bp);
    // check_free_list();

    //update previous block in list
    if (GET_PREVIOUS(bp) != NULL)
        PUT_POINTER((GET_PREVIOUS(bp)), GET_NEXT(bp));
    else
        GET_LIST(num) = (typeof(GET_LIST(num)))GET_NEXT(bp);

    //update next block in list
    if (GET_NEXT(bp) != NULL)
        PUT_POINTER(GO_PREVIOUS(GET_NEXT(bp)), GET_PREVIOUS(bp));

    //check_free_list();
    //printf("End of remove_block: %p\n\n", bp);
}

static void add_to_free_list(unsigned long **bp) {


    int num = which_list((void *)bp);
    //printf("\nBeginning of add_to_free_list: %p\n", bp);
    //check_free_list();

    //set the previous pointer of our free block to null
    PUT_POINTER(GO_PREVIOUS(bp), NULL);

    //set next pointer of new free block to current head of free list;
    if (GET_LIST(num) != NULL) {
        PUT_POINTER(GO_NEXT(bp), GET_LIST(num));

        //sets the
        PUT_POINTER(GO_PREVIOUS(GET_LIST(num)), bp);
    } else {
        PUT_POINTER(GO_NEXT(bp), NULL);
    }

    //set head of free list to new free block;
    GET_LIST(num) = bp;

    //check_free_list();
    //printf("End of add_to_free_list: %p\n\n", bp);
}

// coalesce - Boundary tag coalescing. Return ptr to coalesced block

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (!prev_alloc) {
        //remove prev
        remove_block_from_list((unsigned long *) PREV_BLKP(bp));
    }

    if (!next_alloc) {
        //remove next
        remove_block_from_list((unsigned long *) NEXT_BLKP(bp));
    }

    if (prev_alloc && next_alloc) {              /* Case 1 */
        //This is the second shit triggering infiloop
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
    remove_block_from_list(bp);
    if ((csize - asize) >= MIN_SIZE) {
        //HERE IS THE SHIT
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        //HERE THE SHIT ENDS
        if(GET_ALLOC(NEXT_BLKP(bp))){
            printf("HERE");
        }
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        add_to_free_list((unsigned long **)bp);                    // Jasper, Hynes
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


// find_fit - Find a fit for a block with asize bytes

static int which_list(void* bp){

    //extract the size of the block pointer

    //call which list asze to figure out list number

    return 0;
}


static int which_list_asize(int size){

    //figure out which segmented list it goes into

    //return that list #

    return 0;
}

static void *find_fit(size_t asize) {
    /* First fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            //here was the remove_block but we will move it to place()
            return bp;
        }
    }
    return NULL; /* No fit */

}


static void *find_fit_segmented(size_t asize) {

    int num = which_list_asize(asize);
    // first fit explicit list
    unsigned long **bp = GET_LIST(num);
    for (bp; GO_NEXT(bp) != NULL; bp = (typeof(bp))GET_NEXT(bp)) {
        if ((asize <= GET_SIZE(HDRP(bp)))) {
            // error statement when block is taken

            return bp;
        }
    }
    return NULL;
}








//print functions

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
    if ((size_t) bp % 8) {
        printf("Error: %p is not doubleword aligned\n", bp);
    }

    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("Error: %p header does not match footer\n", bp);
    }
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

static void check_free_list() {
    printf("==============================\n");
    printf("FREE LIST CHECK START:\n");

    unsigned long **fp = free_list_head;

    printf("------------------------------\n");
    printf("Free List Head: %p\n", free_list_head);
    printf("------------------------------\n");

    for (fp; fp != NULL; fp = GET_NEXT(fp)) {

        size_t hsize, halloc, fsize, falloc;

        hsize = GET_SIZE(HDRP(fp));
        halloc = GET_ALLOC(HDRP(fp));
        fsize = GET_SIZE(FTRP(fp));
        falloc = GET_ALLOC(FTRP(fp));

        printf("Address: \t%p\n", fp);
        printf("header: \t[%zu:%c]\n", hsize, (halloc ? 'a' : 'f'));
        printf("Next_Ptr: \t%p\n", GET_NEXT(fp));
        printf("Prev_Ptr: \t%p\n", GET_PREVIOUS(fp));
        printf("footer: \t[%zu:%c]\n", fsize, (falloc ? 'a' : 'f'));

        if ((size_t) fp % 8) {
            printf("Error: %p is not doubleword aligned\n", fp);
        } else {
            printf("Double-Word aligned: \tTrue.\n");
        }

        if (GET(HDRP(fp)) != GET(FTRP(fp))) {
            printf("Error: header does not match footer\n");
        } else {
            printf("Header matches footer: \tTrue.\n");
        }



        if (GET_NEXT(fp) == NULL) {
            printf("----------\n");
            printf("--End of Free List--\n");
            printf("----------\n");
            printf("----------\n");
        } else {
            printf("----------\n");
        }
    }

    printf("FREE LIST CHECK END.\n");
    printf("==============================\n\n\n");
}