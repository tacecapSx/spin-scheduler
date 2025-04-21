#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdint.h>
#include <unistd.h>

#include "types.h"
#include "heap.h"

#define MAX_TASKS 4

#define THREAD_COUNT 2

#define NEW 0
#define RUNNING 1
#define BLOCKED 2
#define TERMINATED 3

// Global heap
Heap task_heap;

// Global mutexes
pthread_mutex_t heap_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t log_file_mutex = PTHREAD_MUTEX_INITIALIZER;

// Log file
FILE *log_file;

void log_task(FILE* log_file, Task task) {
    pthread_mutex_lock(&log_file_mutex);
    fprintf(log_file, "    {\"id\": %d, \"state\": %d, \"hash\": %d, \"hash_start\": %d, \"hash_end\": %d, \"hash_progress\": %d, \"priority\": %d},\n", 
            task.id, task.state, task.hash, task.hash_start, task.hash_end, task.hash_progress, task.p);

    fflush(log_file);

    pthread_mutex_unlock(&log_file_mutex);
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
}

void* task_runner(void* arg) {
    while (1) {
        pthread_mutex_lock(&heap_mutex);
        
        // If heap is empty, unlock and terminate
        if (heap_is_empty(&task_heap)) {
            pthread_mutex_unlock(&heap_mutex);
            break;
        }

        Task task = heap_get_max(&task_heap);
        pthread_mutex_unlock(&heap_mutex);

        task.state = RUNNING;
        log_task(log_file, task);

        task.hash_progress++;

        usleep(1000); // Sleep for a bit to stimulate interleaving (in this time, other threads can start work)

        if (murmurhash3_32(task.hash_progress) == task.hash) {
            task.state = TERMINATED;
            log_task(log_file, task);
        } else {
            task.state = BLOCKED;
            log_task(log_file, task);

            // Reinsert the task safely
            pthread_mutex_lock(&heap_mutex);
            heap_insert(&task_heap, task);
            pthread_mutex_unlock(&heap_mutex);
        }
    }

    return NULL;
}

void run_scheduler() {
    log_file = fopen("scheduler/scheduler_trace.json", "w");
    fprintf(log_file,"{\n\"events\": [\n");
    
    pthread_t threads[THREAD_COUNT];

    for (int i = 0; i < THREAD_COUNT; i++) {
        pthread_create(&threads[i], NULL, task_runner, NULL);
    }

    for (int i = 0; i < THREAD_COUNT; i++) {
        pthread_join(threads[i], NULL);
    }

    fseek(log_file, -2, SEEK_CUR); // Overwrite the trailing comma
    fprintf(log_file,"\n]\n}");
    fclose(log_file);
    printf("All tasks completed\n");
}

int main(int argc, char *argv[]) {
    // Initialize heap
    heap_init(&task_heap, MAX_TASKS);
    
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
