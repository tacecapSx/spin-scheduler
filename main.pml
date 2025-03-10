#define MAX_TASKS 3

byte task_count = MAX_TASKS;
int task_burst[MAX_TASKS] = {300, 200, 100}; // Initial burst times
byte executed[MAX_TASKS] = {0, 0, 0}; // Tracks if tasks are executed
int recency[MAX_TASKS] = {0, 0, 0}; // Tracks how recently a task has been run (lower is more recent)

active proctype scheduler() {
    byte j = 0;
    byte i = 0;

    do
    :: (task_count > 0) -> 
        atomic {
            i = 0;
            do
            :: (i < task_count) ->
                printf("Running Task %d (Burst Time: %d)\n", i+1, task_burst[i]);

                assert(task_burst[i] > 0); // No completed task runs again
                assert(recency[i] < MAX_TASKS); // Round-robin assertion (no task has not been executed for more than MAX_TASKS)

                task_burst[i] = task_burst[i] - 1;
                executed[i] = 1; // Mark task as executed

                // Update recency
                j = 0;
                do
                :: (j < task_count) ->
                    recency[j]++;
                    j++;
                :: else -> break;
                od;

                recency[i] = 0; // This task just got executed

                if
                :: (task_burst[i] == 0) ->
                    printf("Task %d completed\n", i+1);
                    task_count--;

                    // Shift tasks left
                    j = i;
                    do
                    :: (j < task_count) -> 
                        task_burst[j] = task_burst[j + 1];
                        executed[j] = executed[j + 1];
                        recency[j] = recency[j + 1];
                        j++;
                    :: else -> break;
                    od;
                :: else -> skip;
                fi;

                i++;
            :: else -> break;
            od;
        }
    :: else -> break;
    od;
    printf("All tasks completed\n");

    // nsure every task executed at least once
    assert(executed[0] == 1);
    assert(executed[1] == 1);
    assert(executed[2] == 1);
}

init {
    run scheduler();
}
