#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
        return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
        return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
        set_state(fp,FENCEPOST);
        set_size(fp, ALLOC_HEADER_SIZE);
        fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}
//healper

int get_start_index(int actual_size) {
  int index_start = (actual_size - ALLOC_HEADER_SIZE) / 8 -1;
  if (index_start > N_LISTS-1){
    index_start = N_LISTS - 1; //ok
  }
  return index_start;
}
//insert node into list
static inline void insert_node_into_list(header * ptr, int new_index) {
  header * sent = &freelistSentinels[new_index];
        
        (ptr->next) = sent->next;
        sent->next = ptr;
        ptr->prev = sent;
        (ptr->next)->prev = ptr;
}
//delete node from list
static inline void delete_node_from_list(header * ptr){
  (ptr->prev)->next = ptr->next;
  (ptr->next)->prev = ptr->prev;
}
/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline int find_actual_size(size_t raw_size) {
  
  // rounding to a multiple of 8
  int actual_size = ((raw_size + 7) & ~0x7);
  //adding the size of the required metadata
  actual_size = actual_size + ALLOC_HEADER_SIZE;
  //if smaller than header struct, choosing header struct as size
  if (actual_size < sizeof(header)) {
    actual_size = sizeof(header);
  }
  return actual_size;
}
static header * create_chunk() {
  header *totalBlockAllocated = NULL;
    header * new_chunk = NULL;
  header *justFound = NULL;
      new_chunk = allocate_chunk(ARENA_SIZE);
      bool flag = false;
      if (get_right_header(lastFencePost) == get_left_header(new_chunk)) {
        //when the new chunk and old chunk are in continuous memory
        if (get_state(get_left_header(lastFencePost)) == UNALLOCATED) {
          //case1 : coalesce left and right blocks
          int curr_index = get_start_index(get_size(get_left_header(lastFencePost)));
          header * temp_header = get_left_header(lastFencePost);
          size_t curr_size = get_size(get_left_header(lastFencePost)) + 2 * ALLOC_HEADER_SIZE + get_size(new_chunk);
          set_size(temp_header, get_size(get_left_header(lastFencePost)) + 2 * ALLOC_HEADER_SIZE + get_size(new_chunk));
          lastFencePost = get_right_header(new_chunk);
          lastFencePost->left_size = curr_size;
          int new_index = get_start_index(get_size(temp_header));
          if (curr_index != new_index) {
            delete_node_from_list(temp_header);
            insert_node_into_list(temp_header, get_start_index(get_size(temp_header)));
          }
          justFound = temp_header;
        }
        else if (get_state(get_left_header(lastFencePost)) == ALLOCATED) {
          //case 2: dont coalesce
          header * temp_ptr = lastFencePost;
          set_size_and_state(lastFencePost, get_size(new_chunk) + 2 * ALLOC_HEADER_SIZE, UNALLOCATED);
          insert_node_into_list(temp_ptr, get_start_index(get_size(lastFencePost)));
          lastFencePost = get_header_from_offset(lastFencePost, get_size(new_chunk) + (2 * ALLOC_HEADER_SIZE));
          lastFencePost->left_size =  get_size(new_chunk) + 2 * ALLOC_HEADER_SIZE;
          justFound = temp_ptr;
        }
        

      }else{
        //when the new chunk is away
        insert_os_chunk(get_left_header(new_chunk));
        insert_node_into_list(new_chunk, get_start_index(get_size(new_chunk)));
        flag == true;
        justFound = new_chunk;
      }
    return justFound;

}
static inline header * allocate_object(size_t raw_size) {
  if (raw_size == 0){
    return NULL;
  }
  int actual_size = find_actual_size(raw_size);
  //skipping over smaller objects
  int index_start = get_start_index(actual_size);
  // running a loop to find the required sentinel
  //assuming that there are available blocks in a freelist
  header * sentinelptr = &freelistSentinels[index_start];
  header * ptr = &freelistSentinels[index_start];
  int available = 1;
    while (ptr->next == ptr && index_start < N_LISTS) {
      index_start++;
      if (index_start != N_LISTS)  {
      ptr = &freelistSentinels[index_start];
    }
    }
    if (index_start == N_LISTS-1){
      while (get_size(ptr) < actual_size) {
        ptr = ptr->next;
      }
    }
    if (index_start == N_LISTS) {
      available = 0;
    }
  
  //allocating new chunk when not found
  header * justFound = NULL;
  if (available == 0) {
     justFound = create_chunk();
  }
  if (justFound != NULL) {
    ptr = justFound;
  }
  //when sizeof block is exactly equal to actual_size
  //case 1
  if (get_size(ptr) == actual_size){
    set_state(ptr, ALLOCATED);
    set_size(ptr, actual_size); //?
    
    (ptr->prev)->next = ptr->next;
    (ptr->next)->prev = ptr->prev;
    header * p2 = (header *)ptr->data;
    return p2;
  }
  //when size of block is greater than actual
  //case 2
  if (get_size(ptr) > actual_size) {
    int offset = get_size(ptr) - actual_size;
    header * new_header = get_header_from_offset(ptr, offset);
  
    set_state(new_header, ALLOCATED);
    set_size(new_header, actual_size);
    new_header->left_size = offset; //?
   
    int curr_index = get_start_index(get_size(ptr));
    set_size(ptr, offset);
    get_right_header(new_header)->left_size = actual_size; //?
    int new_index = get_start_index(get_size(ptr));
    if (curr_index != new_index) {
      //remove from current freelist
      delete_node_from_list(ptr);
      
      //insert into linked list
      insert_node_into_list(ptr, new_index);
      
    }
    return (header *)(new_header->data);
    
 
  }
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  if (p == NULL) {
    return;
  }
  header * ptr = ptr_to_header(p);
  if (get_state(ptr) == UNALLOCATED) {
    fprintf(stderr, "Double Free Detected\n");
    assert(false);
    }
  header * left_ptr = get_left_header(ptr);
  header * right_ptr = get_right_header(ptr);
  size_t left_header_size = get_size(left_ptr);
 // size_t right_header_size = get_size(right_ptr);
  set_state(ptr, UNALLOCATED);

  //case 1
  if (get_state(left_ptr) == UNALLOCATED && get_state(right_ptr) == UNALLOCATED) {
    //coalesce all
    (get_right_header(right_ptr))->left_size = left_header_size + get_size(ptr) + get_size(right_ptr);
    delete_node_from_list(right_ptr);
    int curr_index = get_start_index(get_size(left_ptr));
    set_size(left_ptr, left_header_size + get_size(right_ptr)  + get_size(ptr));
    int new_index = get_start_index(get_size(left_ptr));
    if (curr_index != new_index) {
      delete_node_from_list(left_ptr);
      insert_node_into_list(left_ptr, new_index);
    }
    return;
  }

  //case 2
  if (get_state(left_ptr) == UNALLOCATED && get_state(right_ptr) != UNALLOCATED) {
    //coalesce left and ptr
    (right_ptr->left_size = left_header_size + get_size(ptr));
    int curr_index = get_start_index(get_size(left_ptr));
    set_size(left_ptr, left_header_size + get_size(ptr));
    int neww_index = get_start_index(get_size(left_ptr));
    if (neww_index != curr_index) {
      delete_node_from_list(left_ptr);
      insert_node_into_list(left_ptr, neww_index);
    }
    return;
  }

  //case 3
  if (get_state(right_ptr) == UNALLOCATED && get_state(left_ptr) != UNALLOCATED){
    (get_right_header(right_ptr))->left_size = get_size(ptr) + get_size(right_ptr);
    delete_node_from_list(right_ptr);
    set_size(ptr, get_size(ptr) + get_size(right_ptr));
    int new_index = get_start_index(get_size(ptr));
    insert_node_into_list(ptr, new_index);

    return;
  }
  
    int index = get_start_index(get_size(ptr));
    insert_node_into_list(ptr, index);
    return;


  // TODO implement deallocation
  // (void) p;
  // assert(false);
  // exit(1);
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
        if (get_state(chunk) != FENCEPOST) {
                fprintf(stderr, "Invalid fencepost\n");
                print_object(chunk);
                return chunk;
        }
        
        for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
                if (get_size(chunk)  != get_right_header(chunk)->left_size) {
                        fprintf(stderr, "Invalid sizes\n");
                        print_object(chunk);
                        return chunk;
                }
        }
        
        return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}