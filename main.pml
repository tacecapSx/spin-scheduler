// Model that mimics the behavior of main.c

#include "spin_random_inputs.pml"

#define NEW 0
#define RUNNING 1
#define BLOCKED 2
#define TERMINATED 3

typedef Task {
  int id;
  byte state;
  int hash;
  int hash_start;
  int hash_end;
  int hash_progress;
  byte p
};

Task task_data[MAX_TASKS];
Task task_queue[MAX_TASKS];
byte task_count = 0;

int execution_time = 0;

inline murmurhash3_32(key, k) {
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

inline add_task(task_id, task_hash, task_hash_start, task_hash_end, task_p) {
  if
  :: task_count < MAX_TASKS ->
    task_data[task_count].state = NEW;
    task_data[task_count].id = task_id;
    task_data[task_count].hash = task_hash;
    task_data[task_count].hash_progress = task_hash_start - 1;
    task_data[task_count].hash_start = task_hash_start;
    task_data[task_count].hash_end = task_hash_end;
    task_data[task_count].p = task_p;

    task_queue[task_count].state = NEW;
    task_queue[task_count].id = task_id;
    task_queue[task_count].hash = task_hash;
    task_queue[task_count].hash_progress = task_hash_start - 1;
    task_queue[task_count].hash_start = task_hash_start;
    task_queue[task_count].hash_end = task_hash_end;
    task_queue[task_count].p = task_p;
    task_count++;
  fi;
}

inline run_scheduler() {
  do
  :: task_count > 0 ->
     d_step {
       // Process each task in round-robin fashion
       byte i = 0;
       do
       :: i < task_count ->
          task_data[task_queue[i].id].state = RUNNING;
          task_queue[i].state = RUNNING;

          // Perform one reverse hash attempt
          execution_time++;

          task_queue[i].hash_progress++;
          
          int hash;
          murmurhash3_32(task_queue[i].hash_progress, hash);

          // Completed if hash is correct
          if
          :: hash == task_queue[i].hash ->
            task_data[task_queue[i].id].state = TERMINATED;
            task_queue[i].state = TERMINATED;
            
            // Remove task
            byte j = i;
            do
            :: j < task_count-1 ->
               task_queue[j].id = task_queue[j+1].id;
               task_queue[j].hash = task_queue[j+1].hash;
               task_queue[j].hash_progress = task_queue[j+1].hash_progress;
               task_queue[j].hash_start = task_queue[j+1].hash_start;
               task_queue[j].hash_end = task_queue[j+1].hash_end;
               task_queue[j].p = task_queue[j+1].p;
               j++;
            :: else -> break;
            od;
            task_count--;
          :: else ->
            task_data[task_queue[i].id].state = BLOCKED;
            task_queue[i].state = BLOCKED;
            i++;
          fi;
       :: else -> break;
       od;
     }
  :: else -> break;
  od;
}

init {
  // Load in tasks from spin_random_inputs.pml
  d_step {
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

#include "ltl_statements.pml"