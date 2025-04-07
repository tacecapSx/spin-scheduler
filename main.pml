#include "spin_input_trail.pml"

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

Task task_queue[MAX_TASKS]
byte task_count = MAX_TASKS;

int id, hash, hash_start, hash_end, hash_progress;
byte state, p;

int execution_time = 0;

inline run_scheduler() {
  do
    :: nempty(trail) ->
      
      trail?id, state, hash, hash_start, hash_end, hash_progress, p;

      task_queue[id].state = state;

      if
      :: state == TERMINATED -> 
          task_count--;
      :: else -> skip;
      fi;
    :: empty(trail) && trail_index < TRAIL_COUNT  ->
      execution_time++;
      
      trail_feeder();
    :: empty(trail) && trail_index >= TRAIL_COUNT -> break;
  od;
}

inline trail_feeder() {
  int i = 0;

  do
  :: i < task_count ->
      d_step {
        //int lol = 0;

        c_code {
          //now.lol = 3;
          
          now.id = trail_data[now.trail_index].id;
          now.state = trail_data[now.trail_index].state;
          now.hash = trail_data[now.trail_index].hash;
          now.hash_start = trail_data[now.trail_index].hash_start;
          now.hash_end = trail_data[now.trail_index].hash_end;
          now.hash_progress = trail_data[now.trail_index].hash_progress;
          now.p = trail_data[now.trail_index].p;
        }

        trail_index++;
        printf("%d\n", trail_index);
        trail!id, state, hash, hash_start, hash_end, hash_progress, p;

        i++;
      }
  :: else -> break;
  od;
}

init {
  // Load in tasks to queue
  run init_trace();

  run_scheduler();
}

#include "ltl_statements.pml"