#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define MAX_TASKS 4

#define NEW 0
#define RUNNING 1
#define BLOCKED 2
#define TERMINATED 3

typedef struct {
    int id;
    uint8_t state;
    int hash;
    int hash_start;
    int hash_end;
    int hash_progress;
    uint8_t p;
} Task;

Task task_queue[MAX_TASKS];
int task_count = 0;

inline void log_task(FILE* log_file, int queue_position, Task task) {
    fprintf(log_file, "    {\"queue_position\": %d, \"id\": %d, \"state\": %d, \"hash\": %d, \"hash_start\": %d, \"hash_end\": %d, \"hash_progress\": %d, \"priority\": %d},\n", 
            queue_position, task.id, task.state, task.hash, task.hash_start, task.hash_end, task.hash_progress, task.p);
}

int murmurhash3_32(int key) {
    const int c1 = 0xcc9e2d51;
    const int c2 = 0x1b873593;
    
    // Mix key
    key *= c1;
    key = (key << 15) | (key >> (32 - 15)); // ROTL32
    key *= c2;
    
    key = (key << 13) | (key >> (32 - 13)); // ROTL32
    key = key * 5 + 0xe6546b64;

    key ^= 4;

    key ^= key >> 16;
    key *= 0x85ebca6b;
    key ^= key >> 13;
    key *= 0xc2b2ae35;
    key ^= key >> 16;

    return key;
}

void add_task(int id, int hash, int hash_start, int hash_end, uint8_t priority) {
    if (task_count < MAX_TASKS) {
        task_queue[task_count].state = NEW;
        task_queue[task_count].id = id;
        task_queue[task_count].hash = hash;
        task_queue[task_count].hash_progress = hash_start - 1;
        task_queue[task_count].hash_start = hash_start;
        task_queue[task_count].hash_end = hash_end;
        task_queue[task_count].p = priority;
        
        task_count++;
    } else {
        printf("Task queue full\n");
    }
}

void run_scheduler() {
    FILE* log_file = fopen("scheduler/scheduler_trace.json", "w");
    fprintf(log_file,"{\n\"events\": [\n");
    
    while (task_count > 0) {
        for (int i = 0; i < task_count; i++) {
            task_queue[i].state = RUNNING;

            // Log task selection
            log_task(log_file, i, task_queue[i]);

            task_queue[i].hash_progress++;
            
            if (murmurhash3_32(task_queue[i].hash_progress) == task_queue[i].hash) { // Hash matches
                task_queue[i].state = TERMINATED;

                // Log task completion
                log_task(log_file, i, task_queue[i]);
                
                task_count--;
                for (int j = i; j < task_count; j++) {
                    task_queue[j] = task_queue[j + 1];
                }

                i--;
            }
            else {
                task_queue[i].state = BLOCKED;

                log_task(log_file, i, task_queue[i]);
            }
        }
    }

    fseek(log_file, -2, SEEK_CUR); // Overwrite the trailing comma
    fprintf(log_file,"\n]\n}");
    fclose(log_file);
    printf("All tasks completed\n");
}

int main(int argc, char *argv[]) {
    // Load random inputs
    FILE *file = fopen("scheduler/scheduler_random_inputs.txt", "r");
    for(int i = 0; i < MAX_TASKS; i++) {
        int id, hash, hash_start, hash_end;
        uint8_t priority;

        if(fscanf(file, "%d %u %d %d %hhd", &id, &hash, &hash_start, &hash_end, &priority))
            add_task(id, hash, hash_start, hash_end, priority);
    }

    fclose(file);

    run_scheduler();
    
    return 0;
}
