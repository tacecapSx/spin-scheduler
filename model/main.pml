// Model that mimics the behavior of main.c

#include "spin_random_inputs.pml"
#include "heap.pml"

#define NEW 0
#define RUNNING 1
#define BLOCKED 2
#define TERMINATED 3

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

chan load_mutex = [1] of {bool};
chan heap_mutex = [1] of {bool};

int execution_time = 0;

inline mutex_lock(mutex) { mutex?_; }
inline mutex_unlock(mutex) { mutex!true; }

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

// Task-running "thread"
proctype task_runner() {
  int hash;
  byte task_index;
  
  do
  :: true ->
    mutex_lock(heap_mutex);
        
    // If heap is empty, unlock and terminate
    if
    :: heap.size == 0 ->
      mutex_unlock(heap_mutex);
      break;
    :: else -> skip;
    fi;

    heap_get_max(task_index);
    mutex_unlock(heap_mutex);
  
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
      mutex_lock(heap_mutex);
      heap_insert(task_index);
      mutex_unlock(heap_mutex);
    fi;
  od;
}

inline run_scheduler() {
  // Start 2 threads
  run task_runner();
  run task_runner();
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
    :: else -> mutex_unlock(load_mutex); break;
    od;
  }

  // Wait for loading to be complete before running scheduler
  mutex_lock(load_mutex);

  run_scheduler();
}

ltl task_count_will_become_zero_and_be_bounded {
  [] (heap.size <= MAX_TASKS)
    &&
  [] <> (heap.size == 0)
}

#include "ltl_statements.pml"