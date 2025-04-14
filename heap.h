#ifndef HEAP_H
#define HEAP_H

#include <stdint.h>
#include "types.h"

#define HEAP_CAPACITY 4  // Default initial capacity of heap

typedef struct {
    Task *data;
    int size;
    int capacity;
} Heap;

void heap_init(Heap *heap, int max_size);
void heap_destroy(Heap *heap);
int heap_is_empty(Heap *heap);
void heap_insert(Heap *heap, Task request);
Task heap_get_max(Heap *heap);
void bubble_up(Heap *heap, int index);
void bubble_down(Heap *heap, int index);

#endif // HEAP_H