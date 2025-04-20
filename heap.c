#include <stdio.h>
#include <stdlib.h>
#include "heap.h"
#include "types.h"

// swap helper function
static inline void swap(Task *a, Task *b) {
    Task temp = *a;
    *a = *b;
    *b = temp;
}

// initialize the heap
void heap_init(Heap *heap, int max_size) {
    heap->data = (Task*) malloc(max_size * sizeof(Task));
    if(!heap->data) {
        perror("Couldn't initialize heap");
        exit(EXIT_FAILURE);
    }
    heap->size = 0;
    heap->capacity = max_size;
}

// destroy the heap and free memory
void heap_destroy(Heap *heap) {
    free(heap->data);
    heap->data = NULL;
    heap->size = 0;
    heap->capacity = 0;
}

inline int heap_is_empty(Heap *heap) {
    return heap->size == 0;
}

// Insert an element into the heap
void heap_insert(Heap *heap, Task task) {
    if (heap->size == heap->capacity) {
        printf("ERROR: Attempted to insert into heap at max capacity.\n");
        exit(EXIT_FAILURE);
    }
    heap->data[heap->size] = task;
    bubble_up(heap, heap->size);
    heap->size++;
}

// get the maximum priority element
Task heap_get_max(Heap *heap) {
    if (heap_is_empty(heap)) {
        fprintf(stderr, "ERROR: Heap is empty; no elements to extract.\n");
        exit(EXIT_FAILURE);
    }
    Task max = heap->data[0];
    heap->data[0] = heap->data[--heap->size];
    bubble_down(heap, 0);
    return max;
}

// restore heap property upwards
void bubble_up(Heap *heap, int index) {
    while (index > 0) {
        int parent = (index - 1) / 2;
        if (heap->data[index].p <= heap->data[parent].p) {
            break;
        }
        swap(&heap->data[index], &heap->data[parent]);
        index = parent;
    }
}

// restore heap property downwards
void bubble_down(Heap *heap, int index) {
    while (index < heap->size) {
        int left = 2 * index + 1;
        int right = 2 * index + 2;
        int largest = index;

        if (left < heap->size && heap->data[left].p > heap->data[largest].p) {
            largest = left;
        }
        if (right < heap->size && heap->data[right].p > heap->data[largest].p) {
            largest = right;
        }
        if (largest == index) {
            break;
        }
        swap(&heap->data[index], &heap->data[largest]);
        index = largest;
    }
}
