#define MAX_TASKS 4

#define NEW 0
#define RUNNING 1
#define BLOCKED 2
#define TERMINATED 3

typedef Task {
  int id;
  byte state;
  int burst_time;
  byte p
};

Task task_queue[MAX_TASKS];
byte task_count = 0;

inline log_state(last) {
  printf("{\n  \"task_count\": %d,\n  \"tasks\": [\n", task_count);
  byte t = 0;
  do
  :: t < task_count ->
    printf("    {\"position\": %d, \"id\": %d, \"state\": %d, \"burst_time\": %d, \"priority\": %d}", 
            t, task_queue[t].id, task_queue[t].state, task_queue[t].burst_time, task_queue[t].p);

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

inline add_task(task_id, burst, prio) {
  if
  :: task_count < MAX_TASKS ->
    task_queue[task_count].state = NEW;
    task_queue[task_count].id = task_id;
    task_queue[task_count].burst_time = burst;
    task_queue[task_count].p = prio;
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
          
          // Decrease burst time
          task_queue[i].burst_time--;
          
          // Check if task completed
          if
          :: task_queue[i].burst_time == 0 ->
            task_queue[i].state = TERMINATED;

            log_state(0);
            
            // Remove task
            byte j = i;
            do
            :: j < task_count-1 ->
               task_queue[j].id = task_queue[j+1].id;
               task_queue[j].burst_time = task_queue[j+1].burst_time;
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

// Main process
init {
  add_task(1, 300, 0);
  add_task(2, 200, 0);
  add_task(3, 100, 0);
  add_task(4, 150, 0);
  run_scheduler();
}

ltl p1 {[] (task_count <= MAX_TASKS)}
ltl p2 {<> (task_count == 0)}
ltl p3 {<> (task_queue[0].state == TERMINATED)}