// Model that mimics the behavior of main.c

#include "spin_random_inputs.pml"
#include "heap.pml"

#define NEW 0
#define RUNNING 1
#define BLOCKED 2
#define TERMINATED 3

#define THREAD_COUNT 2

typedef Task {
  int id;
  byte state;
  bool entered_running;
  int hash;
  int hash_start;
  int hash_end;
  int hash_progress;
  byte p;
  int insertion_order
};

Task task_data[MAX_TASKS];
byte task_count = 0;

chan heap_mutex = [1] of {bool}; // Mutex variable as a message channel
bool heap_locked = false; // Boolean version of the chan for verification

bool in_cs[THREAD_COUNT]; // Boolean for each thread signalling if it is in a critical section
bool waiting[THREAD_COUNT]; // Boolean for each thread signalling if it is waiting to enter a critical section

int execution_time = 0;

// Mutex lock/unlock functions utilizing the message channel. They also set verification-relevant flags using a thread's id.
inline mutex_lock(id)   {
  waiting[id] = true;
  
  d_step {
    heap_mutex?_;
    waiting[id] = false;
    heap_locked = true;
    in_cs[id] = true;
  }
}

inline mutex_unlock(id) {
  d_step {
    heap_mutex!true;
    heap_locked = false;
    in_cs[id] = false;
  }
}

inline murmurhash3_32(key, k) {
  d_step {
    int c1 = 3432918353; //0xcc9e2d51
    int c2 = 461845907;  //0x1b873593
    
    k = key;

    // Mix key
    k = k * c1;
    k = (k << 15) | (k >> (32 - 15)); // ROTL32
    k = k * c2;
    
    k = (k << 13) | (k >> (32 - 13)); // ROTL32
    k = k * 5 + 3864292196; //0xe6546b64

    k = k ^ 4;

    k = k ^ (k >> 16);
    k = k * 2246822507; //0x85ebca6b
    k = k ^ (k >> 13);
    k = k * 3266489909; //0xc2b2ae35
    k = k ^ (k >> 16);
  }
}

inline add_task(task_id, task_hash, task_hash_start, task_hash_end, task_p) {
  d_step {
    task_data[task_count].state = NEW;
    task_data[task_count].id = task_id;
    task_data[task_count].hash = task_hash;
    task_data[task_count].hash_progress = task_hash_start - 1;
    task_data[task_count].hash_start = task_hash_start;
    task_data[task_count].hash_end = task_hash_end;
    task_data[task_count].p = task_p;
    task_data[task_count].insertion_order = -1;
  }

  // Insert into heap safely
  atomic {
    mutex_lock(heap_mutex);
    heap_insert(task_count);
    mutex_unlock(heap_mutex);

    task_count++;
  }
}

// Task-running "thread" with an id
proctype task_runner(byte id) {
  int hash;
  byte task_index;
  
  do
  :: true ->
    mutex_lock(id);
        
    // If heap is empty, unlock and terminate
    if
    :: heap.size == 0 ->
      mutex_unlock(id);
      break;
    :: else -> skip;
    fi;

    heap_get_max(task_index);
    mutex_unlock(id);
  
    d_step {
      execution_time++;

      // Set the entered running signal for verification
      task_data[task_index].entered_running = true;
      task_data[task_index].state = RUNNING;
      task_data[task_index].entered_running = false;

      task_data[task_index].hash_progress++;
    }
    
    murmurhash3_32(task_data[task_index].hash_progress, hash);

    // Completed if hash is correct
    if
    :: hash == task_data[task_index].hash ->
      task_data[task_index].state = TERMINATED;
    :: else ->
      task_data[task_index].state = BLOCKED;

      // Reinsert task index safely
      mutex_lock(id);
      heap_insert(task_index);
      mutex_unlock(id);
    fi;
  od;
}

inline run_scheduler() {
  // Start THREAD_COUNT
  byte id = 0;

  do
  :: id < THREAD_COUNT ->
    run task_runner(id); // Start a thread with its id
    id++;
  :: else -> break;
  od;
}

init {
  // Initialize heap mutex
  mutex_unlock(heap_mutex);
  
  // Load in tasks from spin_random_inputs.pml
  atomic {
    byte task = 0;

    do
    :: task < MAX_TASKS ->
        add_task(task_ids[task], task_hashes[task], task_hash_starts[task], task_hash_ends[task], task_priorities[task]);
        task++;
    :: else -> break;
    od;
  }

  run_scheduler();
}

ltl task_count_will_become_zero_and_be_bounded {
  [] (heap.size <= MAX_TASKS)
    &&
  [] <> (heap.size == 0)
}

#include "ltl_statements.pml"