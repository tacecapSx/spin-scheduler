#ifndef PACKETS_H
#define PACKETS_H

#include <stdint.h>

typedef struct {
    int32_t id;
    uint8_t state;
    int32_t hash;
    int32_t hash_start;
    int32_t hash_end;
    int32_t hash_progress;
    uint8_t p;
    int32_t insertion_order;
} Task;

#endif // PACKETS_H