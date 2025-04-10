#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

#include "types.h"
#include "heap.h"

#define MAX_TASKS 4

#define NEW 0
#define RUNNING 1
#define BLOCKED 2
#define TERMINATED 3

// global heap and mutex / cond
Heap task_heap;
pthread_mutex_t heap_mutex = PTHREAD_MUTEX_INITIALIZER;

int task_count = 0;

void log_task(FILE* log_file, Task task, int last) {
    fprintf(log_file, "    {\"id\": %d, \"state\": %d, \"hash\": %d, \"hash_start\": %d, \"hash_end\": %d, \"hash_progress\": %d, \"priority\": %d}", 
            task.id, task.state, task.hash, task.hash_start, task.hash_end, task.hash_progress, task.p);

    if(!last) {
        fprintf(log_file, ",\n");
    }
    else {
        fprintf(log_file, "\n");
    }
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

void add_task(int id, int hash, int hash_start, int hash_end, char priority) {
    if (task_count < MAX_TASKS) {
        Task task;
        
        task.state = NEW;
        task.id = id;
        task.hash = hash;
        task.hash_progress = hash_start - 1;
        task.hash_start = hash_start;
        task.hash_end = hash_end;
        task.p = priority;

        // lock the heap and insert the task
        pthread_mutex_lock(&heap_mutex);
        heap_insert(&task_heap, task);
        pthread_mutex_unlock(&heap_mutex);
        
        task_count++;
    } else {
        printf("Task queue full\n");
    }
}

void run_scheduler() {
    FILE* log_file = fopen("c_trace.json", "w");
    fprintf(log_file,"{\n\"events\": [\n");
    
    while (task_count > 0) {
        Task task = heap_get_max(&task_heap);

        task.state = RUNNING;

        // Log task selection
        log_task(log_file, task, 0);

        task.hash_progress++;
        
        if (murmurhash3_32(task.hash_progress) == task.hash) { // Hash matches
            task.state = TERMINATED;

            // Log task completion
            log_task(log_file, task, task_count == 1);
            
            task_count--;
        }
        else {
            task.state = BLOCKED;

            // lock the heap and reinsert the task
            pthread_mutex_lock(&heap_mutex);
            heap_insert(&task_heap, task);
            pthread_mutex_unlock(&heap_mutex);
        }
    }

    fprintf(log_file,"]\n}");
    fclose(log_file);
    printf("All tasks completed\n");
}

int main(int argc, char *argv[]) {
    // Initialize heap
    heap_init(&task_heap, HEAP_CAPACITY);
    
    // Load random inputs
    FILE *file = fopen("c_random_inputs.txt", "r");
    for(int i = 0; i < MAX_TASKS; i++) {
        int id, hash, hash_start, hash_end;
        char priority;

        if(fscanf(file, "%d %u %d %d %hhd", &id, &hash, &hash_start, &hash_end, &priority))
            add_task(id, hash, hash_start, hash_end, priority);
    }

    fclose(file);

    run_scheduler();
    
    return 0;
}
