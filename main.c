#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <stdint.h>
#include <string.h>

#define MAX_TASKS 4

#define NEW 0
#define RUNNING 1
#define BLOCKED 2
#define TERMINATED 3

enum SchedulerStrategy {
    ROUND_ROBIN,
    PRIORITY
};

typedef struct {
    int32_t id;
    uint8_t state;
    uint32_t burst_time;
    uint8_t p;
} Task;

Task task_queue[MAX_TASKS];
int task_count = 0;

void log_state(FILE* log_file, int last) {
    fprintf(log_file, "{\n  \"task_count\": %d,\n  \"tasks\": [\n", task_count);
    for (int i = 0; i < task_count; i++) {
        fprintf(log_file, "    {\"position\": %d, \"id\": %d, \"state\": %d, \"burst_time\": %d, \"priority\": %d}", 
               i, task_queue[i].id, task_queue[i].state, task_queue[i].burst_time, task_queue[i].p);

        if(i < task_count - 1) {
            fprintf(log_file, ",\n");
        }
        else {
            fprintf(log_file, "\n");
        }
    }
    
    if(last) {
        fprintf(log_file, "  ]\n}\n");
    }
    else {
        fprintf(log_file, "  ]\n},\n");
    }
}

void add_task(int32_t id, uint32_t burst_time, uint8_t priority) {
    if (task_count < MAX_TASKS) {
        task_queue[task_count].state = NEW;
        task_queue[task_count].id = id;
        task_queue[task_count].burst_time = burst_time;
        task_queue[task_count].p = priority;
        
        task_count++;
    } else {
        printf("Task queue full\n");
    }
}

void run_scheduler() {
    FILE* log_file = fopen("c_trace.json", "w");
    fprintf(log_file,"{\n\"events\": [\n");
    
    while (task_count > 0) {
        log_state(log_file, 0);
        
        for (int i = 0; i < task_count; i++) {
            task_queue[i].state = RUNNING;

            // Log task selection
            log_state(log_file, 0);
            
            task_queue[i].burst_time--;
            
            if (task_queue[i].burst_time == 0) {
                task_queue[i].state = TERMINATED;

                // Log task completion
                log_state(log_file, 0);
                
                task_count--;
                for (int j = i; j < task_count; j++) {
                    task_queue[j] = task_queue[j + 1];
                }

                i--;
            }
            else {
                task_queue[i].state = BLOCKED;
            }
        }
    }
    
    log_state(log_file, 1);
    fprintf(log_file,"]\n}");
    fclose(log_file);
    printf("All tasks completed\n");
}

int main(int argc, char *argv[]) {
    add_task(1, 300, 0);
    add_task(2, 200, 0);
    add_task(3, 100, 0);
    add_task(4, 150, 0);

    run_scheduler();
    
    return 0;
}
