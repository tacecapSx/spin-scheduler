#include "spin_random_inputs.pml"

#define MAX_TASKS 4

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

Task task_queue[MAX_TASKS];
byte task_count = 0;

inline log_state(last) {
  printf("{\n  \"task_count\": %d,\n  \"tasks\": [\n", task_count);
  byte t = 0;
  do
  :: t < task_count ->
    printf("    {\"position\": %d, \"id\": %d, \"state\": %d, \"hash\": %d, \"hash_start\": %d, \"hash_end\": %d, \"hash_progress\": %d, \"priority\": %d}", 
            t, task_queue[t].id, task_queue[t].state, task_queue[t].hash, task_queue[t].hash_start, task_queue[t].hash_end, task_queue[t].hash_progress, task_queue[t].p);

    if
    :: t < task_count - 1 ->
        printf(",\n");
    :: else ->
        printf("\n");
    fi;
     
    t++;
  :: else -> break;
  od;

  if :: last == 1 ->
    printf("  ]\n}\n");
  :: else ->
    printf("  ]\n},\n");
  fi;
}

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
  printf("{\n\"events\": [\n");
  
  do
  :: task_count > 0 ->
     atomic {
       log_state(0);

       // Process each task in round-robin fashion
       byte i = 0;
       do
       :: i < task_count ->
          task_queue[i].state = RUNNING;

          log_state(0);

          // Perform one reverse hash attempt
          task_queue[i].hash_progress++;
          
          int hash;
          murmurhash3_32(task_queue[i].hash_progress, hash);

          // Completed if hash is correct
          if
          :: hash == task_queue[i].hash ->
            task_queue[i].state = TERMINATED;

            log_state(0);
            
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
            task_queue[i].state = BLOCKED;
            i++;
          fi;
       :: else -> break;
       od;
     }
  :: else -> break;
  od;
  
  log_state(1);
  printf("]\n}");
}

init {
  // Load in tasks from spin_random_inputs.pml
  byte task = 0;

  do
  :: task < MAX_TASKS ->
    add_task(task_ids[task], task_hashes[task], task_hash_starts[task], task_hash_ends[task], task_priorities[task]);
    task++;
  :: else -> break;
  od;

  run_scheduler();
}

#include "ltl_statements.pml"