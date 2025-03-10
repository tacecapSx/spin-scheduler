#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <stdint.h>
#include <string.h>

#define MAX_TASKS 3

enum SchedulerStrategy {
    ROUND_ROBIN,
    PRIORITY
};

typedef struct {
    int32_t id;
    uint32_t burst_time;
    uint8_t priority;
} Task;

Task task_queue[MAX_TASKS];
int task_count = 0;

void add_task(int32_t id, uint32_t burst_time, uint8_t priority) {
    if (task_count < MAX_TASKS) {
        task_queue[task_count].id = id;
        task_queue[task_count].burst_time = burst_time;
        task_queue[task_count].priority = priority;
        
        task_count++;
    } else {
        printf("Task queue full\n");
    }
}

void run_scheduler(int verbose) {
    while (task_count > 0) {
        for (int i = 0; i < task_count; i++) {
            if(verbose)
                printf("Running Task %d (Burst Time: %d)\n", task_queue[i].id, task_queue[i].burst_time);
            
            task_queue[i].burst_time--;
            if (task_queue[i].burst_time == 0) {
                if(verbose)
                    printf("Task %d completed\n", task_queue[i].id);
                
                for (int j = i; j < task_count - 1; j++) {
                    task_queue[j] = task_queue[j + 1];
                }

                task_count--;
                i--;
            }

            sleep(0.01);
        }
    }

    printf("All tasks completed\n");
}

int main(int argc, char *argv[]) {
    int verbose = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-v") == 0) {
            verbose = 1;
        }
    }

    add_task(1, 300UL, 0);
    add_task(2, 200UL, 0);
    add_task(3, 100UL, 0);

    run_scheduler(verbose);
    
    return 0;
}
