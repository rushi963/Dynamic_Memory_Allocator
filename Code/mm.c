/* Team member 1 - Name - Omkar Damle
 *		     ID - 201401114
 * Team member 2 - Name - Rushikesh Nalla
 *		     ID - 201401106
 *
 * Important points: 
 * Simple, 32-bit and 64-bit clean allocator based on an segregated free lists. 
 * Segregated fits approach  
 * LIFO ordering and Pseudo best fit placement policy used in each of the individual free lists which are implemented as explicit lists.
 * Boundary tag coalescing. 
 * Inplace reallocation is used wherever possible.
 * 
 * Blocks are aligned to double-word boundaries.  This yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 *
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"united",
	/* First member's full name */
	"Omkar Damle",
	/* First member's email address */
	"201401114@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Rushikesh Nalla",
	/* Second member's email address (leave blank if none) */
	"201401106@daiict.ac.in"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */


#define MAXSIZE_CLASS_0 (8 * WSIZE)
#define MAXSIZE_CLASS_1 (16 * WSIZE)
#define MAXSIZE_CLASS_2 (32 * WSIZE)
#define MAXSIZE_CLASS_3 (64 * WSIZE)
#define MAXSIZE_CLASS_4 (128 * WSIZE)
#define MAXSIZE_CLASS_5 (256 * WSIZE)
#define MAXSIZE_CLASS_6 (512 * WSIZE)
#define MAXSIZE_CLASS_7 (1024 * WSIZE)
#define MAXSIZE_CLASS_8 (2048 * WSIZE)
#define MAXSIZE_CLASS_9 (4096 * WSIZE)

#define NO_SEG_CLASSES 10

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  
#define MIN(x, y)  ((x) < (y) ? (x) : (y))  


/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Get next/prev free block pointers in explicit free list from given free block*/
#define EXP_GET_PREV_BLKP(bp) GET((unsigned int**)bp)
#define EXP_GET_NEXT_BLKP(bp) GET((unsigned int**)(bp) + 1)

/* Set next/prev free block pointers in explicit free list from given free block*/
#define EXP_SET_NEXT_BLKP(bp, next_block_ptr) PUT((unsigned int**)(bp) + 1, next_block_ptr)
#define EXP_SET_PREV_BLKP(bp, prev_block_ptr) PUT((unsigned int**)bp, prev_block_ptr) 

/* Global variables: */
static char *heap_listp; /* Pointer to first block */  
static unsigned int** segregation_classes;	/*used to keep reference of the segregation classes */

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

/*functions defined exclusively for segregated list implementation*/
static void add_block_in_segregated_list(void* bp , int class);
static void remove_from_list(void* bp, int class);
static void place_segregated_list(void* bp ,size_t asize);
static int get_class_from_size(size_t asize);
static int get_class(void* bp);
static size_t extra_realloc_size(size_t size);
static void* find_fit_by_class_pseudo_best_fit(size_t asize , int class);

/* Function prototypes for heap consistency checker routines: The functions have been commented but they work correctly*/
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 
static void check_pointers_in_heap(bool verbose);
static void check_freelist_completeness(bool verbose);
static void mm_check_coalescing(bool verbose);
static void mm_check_free(bool verbose);

/* 
 * Requires:
 *   None.
 *
 * Effects:	
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 *   Note- we are using segregated free list. So we need to make some space for the pointers to the first item in each list i.e. an array 
 *   of pointers to the various segregation classes.
 */

	int
mm_init(void) 
{

	int n  = NO_SEG_CLASSES; 					//no of segregation classes

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(4 * WSIZE + n * WSIZE)) == (void *)-1)
		return (-1);

	segregation_classes = (unsigned int**) heap_listp;		//setting the array of pointers to free lists
	int i;

	for(i=0;i<n;i++)
		segregation_classes[i] = NULL;				//inititalise all pointers to be null

	heap_listp = (char *)(&segregation_classes[n-1] + 1);		
	//now the alignment padding and prologue and epilogue come into picture 

	PUT(heap_listp, 0);                          			/* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); 			/* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); 			/* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     			/* Epilogue header */
	heap_listp += (2 * WSIZE);


	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	return (0);
}

/* Requires : 1. block pointer of block to be removed from free list 
 *            2. segregated class from which the block pointer is being removed
 * Effects : This function is used to remove a block from its segregated free list class as it is going to be allocated.
 */

void remove_from_list(void* bp, int class)			//note bp points to word after header in block
{

	unsigned int** prev = (unsigned int**)EXP_GET_PREV_BLKP((unsigned int**)bp);	//get the prev free block in list
	unsigned int** next = (unsigned int**)EXP_GET_NEXT_BLKP((unsigned int**)bp);	//get the next free block in list

	//asssumption prev and next point to word after header of prev/next block
	if(prev != NULL)
	{
		*(prev + 1) = (unsigned int*)next;		//change the next field of prev block 
	}
	else
	{	
		//as the block being removed is the header, we need to initialise the header to next block
		segregation_classes[class] = (unsigned int*)next;	
	}

	if(next != NULL)
	{	
		*(next) = (unsigned int*)prev;			//change the prev field of next block
	}
	else
	{
		//as the block being removed is the last one in the list, we don't need to do anything	
	}
}

/* Requires : 1. block pointer of block to be added from free list 
 *            2. segregated class to which the block pointer is being added
 * Effects : This function is used to add a block to its segregated free list class. The block is added to the beginning of the list because of * LIFO strategy used.
 */


void add_block_in_segregated_list(void* bp , int class)
{	

	EXP_SET_PREV_BLKP((unsigned int**)bp, (uintptr_t)NULL);                  //since its the first in the list, its prev field is made NULL.

	EXP_SET_NEXT_BLKP((unsigned int**)bp, (uintptr_t)segregation_classes[class]);  // next field is initialised.

	//assumption : segregation classes contain pointer to word after header.
	if(segregation_classes[class] != NULL)
	{
		*((unsigned int**)segregation_classes[class]) = (unsigned int*)bp;		//prev field of the earlier first member is initialised.
	}
	else
	{
		// do nothing if list was empty inititally.
	}

	segregation_classes[class] = (unsigned int*)bp;				//new block is made the first member of the list.

}

/* Requires : a block pointer
 * Effects : given a free block return its class
 */

static int get_class(void* bp)
{
	size_t asize = GET_SIZE(HDRP(bp));
	return get_class_from_size(asize);
}

/* Requires : a block pointer
 * Effects : given size of block return its class
 */
static int get_class_from_size(size_t asize)
{
	int i;

	if(asize<= MAXSIZE_CLASS_0)
		i=0;
	else if(asize<= MAXSIZE_CLASS_1)
		i=1;
	else if(asize<= MAXSIZE_CLASS_2)
		i=2;
	else if(asize<= MAXSIZE_CLASS_3)
		i=3;
	else if(asize<= MAXSIZE_CLASS_4)
		i=4;
	else if(asize<= MAXSIZE_CLASS_5)
		i=5;
	else if(asize<= MAXSIZE_CLASS_6)
		i=6;
	else if(asize<= MAXSIZE_CLASS_7)
		i=7;
	else if(asize<= MAXSIZE_CLASS_8)
		i=8;
	else 		
		i=9;
	return i;
}



/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */

void *mm_malloc(size_t size) 
{

	//check heap for consistency
	//checkheap(0);	

	size_t asize;      						/* Adjusted block size */
	size_t extendsize; 						/* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;							//minimum block size is 4 words
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);		


	/* let us find the segregated class which fits this allocation request */

	int i= get_class_from_size(asize);

	for(; i<=NO_SEG_CLASSES - 1 ; i++)						//loop through larger classes if suitable free block 												//not found
	{
		bp = find_fit_by_class_pseudo_best_fit(asize , i);			//find suitable free block in segregated class 'i'

		if(bp!=NULL)			
		{	//if we find a suitable class.
			// function for removing 'to be allocated' block from segregated free list. 
			remove_from_list(bp,i);			
			place_segregated_list(bp ,asize);			
			return bp;
		}		
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	remove_from_list(bp, get_class(bp));
	place_segregated_list(bp , asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));

	PUT(HDRP(bp), PACK(size, 0));			//make allocated bit 0 in header
	PUT(FTRP(bp), PACK(size, 0));			//make allocated bit 0 in footer
	coalesce(bp);

	//check_freelist_completeness();
	//checkheap(0);

}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *mm_realloc(void *ptr, size_t size)
{
	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	//If the realloc'd block has previously been given more size than it needs, then
	//this realloc request may be serviced within the same block. This will save us time.

	size_t currSize = GET_SIZE(HDRP(ptr));

	if(size < currSize - 2*WSIZE)			//because size given in realloc request doesnt contain the header and footer, we add 								//2*WSIZE
		return ptr;				//return same ptr as reallocated size is less than existing size

	void* next = NEXT_BLKP(ptr);
	int next_alloc = GET_ALLOC(HDRP(next));		//check if next block is free.

	size_t coalesce_size = GET_SIZE(HDRP(next)) + GET_SIZE(HDRP(ptr));	

	if(!next_alloc && size < coalesce_size - 2*WSIZE)			//if next block is free and total size of this block and next 											//block is enough to satisfy request
	{
		remove_from_list(next, get_class(next));
		PUT(HDRP(ptr) , PACK(coalesce_size , 1));
		PUT(FTRP(ptr) , PACK(coalesce_size , 1));
		return ptr;
	}

	//now if we cant realloc in place, then we need to malloc. While mallocing make sure you keep some extra space at the end of the block
	//so that if a new reallocation request comes, it can be handled in place.
	size_t newSize = extra_realloc_size(size);	
	//size_t newSize = size;

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(newSize));
		
		
	void* oldptr = ptr;
	void* newptr ;
	size_t copySize ;

	newptr = mm_malloc(newSize);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return (NULL);

	/* Copy the old data. */
	copySize = GET_SIZE(HDRP(oldptr));

	if (size < copySize)
		copySize = size;
	memcpy(newptr, oldptr, copySize);

	/* Free the old block. */
	mm_free(oldptr);

	return (newptr);
}


static size_t extra_realloc_size(size_t size)
{
	size_t biggerBuffer = size * 16; 

	//But we will clamp that extra amount in multiples of page size
	if (biggerBuffer > size + 24576) { //currently at 6 pages
		biggerBuffer = size + 24576;
	}

	return biggerBuffer;

}




/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block. Also it needs to add the blocks in appropriate free lists.
 */
	static void *
coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	int class = get_class(bp);

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		add_block_in_segregated_list(bp , class);		
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		remove_from_list( NEXT_BLKP(bp), get_class(NEXT_BLKP(bp)));	
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		add_block_in_segregated_list(bp , get_class(bp));		//class may be changed
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		remove_from_list( PREV_BLKP(bp), get_class(PREV_BLKP(bp)));		
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		add_block_in_segregated_list(bp , get_class(bp));		//class may be changed
	} else {                                        /* Case 4 */
		remove_from_list( NEXT_BLKP(bp), get_class(NEXT_BLKP(bp)));	
		remove_from_list( PREV_BLKP(bp), get_class(PREV_BLKP(bp)));		
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		add_block_in_segregated_list(bp , get_class(bp));		//class may be changed
	}
	return (bp);
}

/* 
 * Requires: number of words by which to extend heap   
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
	static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */			

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires: 1. adjusted block size 
 *  	     2. class in which fit is to be found  
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */

static void* find_fit_by_class_pseudo_best_fit(size_t asize , int class)
{

	//curr points to the word after header of current block
	unsigned int** curr = (unsigned int**)segregation_classes[class] ;		
	//segregation classes array pointers point to the word following the header of first item in list.

	size_t min_padding = 999999999, padding;
	unsigned int** best = NULL ;
	int count = 0 , max_suitable = 5;		//max no of suitable blocks checked in pseudo best fit is 5 

	while(curr!=NULL)				//while we don't reach epilogue block
	{
		if (asize <= GET_SIZE(HDRP(curr)))		
		{							// 'suitable' block
			if(count > max_suitable)			// if 5 suitable blocks have been found return the best one.
				return (best);

			padding = GET_SIZE(HDRP(curr)) - asize ;

			if(padding < min_padding )		
			{min_padding = padding;		
				best = curr;			
			}
			count++ ;	
		}
		curr = (unsigned int**)EXP_GET_NEXT_BLKP(curr);			// move on to the next free block in same class	
	}	

	//we have finished searching the given class but did not find any appropriate free block. return best=NULL
	return best;

}


/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. The splitted block fragment is added to the appropriate segregation class 
 */
static void place_segregated_list(void* bp ,size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (2 *DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));

		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));			/*we need to put the fragment in appropriate class*/
		PUT(FTRP(bp), PACK(csize - asize, 0));

		size_t free_block_size = csize - asize;		
		int i;

		i = get_class_from_size(free_block_size);	

		// add fragment in segregated class		

		add_block_in_segregated_list(bp , i);

	} else {
		PUT(HDRP(bp), PACK(csize, 1));				//if no spliting feasible
		PUT(FTRP(bp), PACK(csize, 1));
	}


}




/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
	static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 *Effects : checks if the pointers in a heap block point to valid heap addresses.
 * At the start of the heap we have 10 pointers for each of the segregated classes. Each pointer points to the first member in that particular  
 * class. We will check these pointers. Also each free block contains pointers to other free blocks. We will check those pointers too.
 */

static void check_pointers_in_heap(bool verbose)
{
	int i;
	// we check the segregation list pointers
	for(i=0 ; i < NO_SEG_CLASSES ; i++)
	{
		if(segregation_classes[i]==NULL)
			continue;
		else if((void*)segregation_classes[i] > mem_heap_lo() && (void*)segregation_classes[i] < mem_heap_hi())
			continue;
		else
			{
			printf("Error : segregated list pointers point out of heap !\n");
			if(verbose)
				printf("segregation_classes[%d] contains pointer out of heap",i);
			}	
	}
	// now we check the 2 pointers stored in each free block.
	unsigned int** curr = (unsigned int**)heap_listp ;
	void* next_freeptr;
	void* prev_freeptr ;

	while( GET_SIZE(curr) != 0)							//while we don't reach the epilogue
	{
		if(GET_ALLOC(HDRP(curr)) == 0)						//if its free check its prev and next free blocks
		{	
			prev_freeptr = (void*)EXP_GET_PREV_BLKP(curr);
			next_freeptr = (void*)EXP_GET_NEXT_BLKP(curr);
			if(prev_freeptr > mem_heap_lo() && prev_freeptr < mem_heap_hi() )	
			{}
			else
			{
				if(prev_freeptr!= NULL)
					{
						printf("Error : free block's prev_free pointer point out of heap !\n");
					if(verbose)
						printblock(curr);					
					}
			}
			if(next_freeptr > mem_heap_lo() && next_freeptr < mem_heap_hi())	
			{}
			else
			{
				if(next_freeptr!= NULL)
					{
						printf("Error : free block's next_free pointer point out of heap !\n");
					if(verbose)
						printblock(curr);
					}
			}
		}		
		curr = (unsigned int**)NEXT_BLKP(curr);				//move on to the next block in heap
	}

}


/*Effects : checks if every free block is present in the free list.*/


void check_freelist_completeness(bool verbose)
{
	// now we check the 2 pointers stored in each free block.
	unsigned int** curr = (unsigned int**)heap_listp ;				// heap block list iterator
	int class;
	unsigned int** curr1 ;								// free block list iterator 

	while(GET_SIZE(curr) != 0)							//while we don't reach the epilogue
	{
		if(GET_ALLOC(HDRP(curr)) == 0)						//if its free check if its present in respective free 												//list class
		{	
			class = get_class(curr);
			curr1 = (unsigned int**)segregation_classes[class];	

			// loop through the list and check if curr is present.
			while(curr1!=NULL)
			{
				if(curr1 == curr)
					break;
				curr1 = (unsigned int**)EXP_GET_NEXT_BLKP(curr1);				
			}

			if(curr1 == NULL)
				{		
					printf("Error : free block not present in any segregation free list.");
					if(verbose)
						printblock(curr);
				}
		}		
		curr = (unsigned int**)NEXT_BLKP(curr);
	}


}

/*Effects : Checks whether every block in the free list is marked free*/
void mm_check_free(bool verbose){

	int i;
	for(i = 0; i < NO_SEG_CLASSES; i++) {
		unsigned int **bp = (unsigned int **)segregation_classes[i]; //start from the beginning
		while (bp != NULL) { //go through the linked list

			//check - is the block marked as free?
			if (GET_ALLOC(HDRP(bp)) == 1 || GET_ALLOC(FTRP(bp)) == 1)
				{
					printf("Block is not marked free\n"); 		
					//inconsistent, if in free list, should be marked free.
					if(verbose)
						printblock(bp);				
				}
			bp  = (unsigned int **)EXP_GET_NEXT_BLKP(bp);
		}
	} 
}

/*Effects : Checks whether there are any contiguous free blocks that escaped coalescing */
void mm_check_coalescing(bool verbose){

	int i;
	for(i = 0; i < NO_SEG_CLASSES; i++) {
		unsigned int **bp = (unsigned int **)segregation_classes[i]; //start from the beginning
		while (bp != NULL) { //go through the linked list
			unsigned int **prev = (unsigned int **)PREV_BLKP(bp);
			unsigned int **next = (unsigned int **)NEXT_BLKP(bp);
			//check if the previous and next blocks are allocated.
			if (!(GET_ALLOC(HDRP(prev)) == 1 && GET_ALLOC(HDRP(next)) == 1))
				{				
			printf("Some free block has escaped coalescing\n"); 		
			//inconsistent, if free block escaped coalescing.
					if(verbose)
						printblock(bp);				
				}
			bp  = (unsigned int **)EXP_GET_NEXT_BLKP(bp);
		}
	} 
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Performs a thorough check of the heap for consistency. 
 */
	void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
			!GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");

	check_freelist_completeness(verbose);		//Checks if all free blocks are present in segregated free lists
	check_pointers_in_heap(verbose);		//Checks if all pointers are within heap limits
	mm_check_free(verbose);			//Checks whether every block in the free list is marked free
	mm_check_coalescing(verbose);			//Checks whether there are any contiguous free blocks that escaped coalescing

}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
	static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
			hsize, (halloc ? 'a' : 'f'), 
			fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
