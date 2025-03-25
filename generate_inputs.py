import random
import struct

MAX_TASKS = 4
SEED = 3924305
DIFFICULTY = 400

random.seed(SEED)

def int32_t(value):
    value &= 0xFFFFFFFF
    if value > 0x7FFFFFFF:
        value -= 0x100000000
    return value

def murmurhash3_32(key):
    c1 = 0xcc9e2d51
    c2 = 0x1b873593
    
    key *= c1
    key = int32_t(key)
    key = ((key << 15) & 0xFFFFFFFF) | (key >> (32 - 15))
    key *= c2
    key = int32_t(key)
    
    key = ((key << 13) & 0xFFFFFFFF) | (key >> (32 - 13))
    key = key * 5 + 0xe6546b64
    key = int32_t(key)

    # Finalization
    key ^= 4  # Input length in bytes (4 bytes for uint32_t)

    key ^= key >> 16
    key *= 0x85ebca6b
    key = int32_t(key)
    key ^= key >> 13
    key *= 0xc2b2ae35
    key = int32_t(key)
    key ^= key >> 16
    
    return int32_t(key)

def main():
    tasks = []
    for i in range(MAX_TASKS):
        key = random.randint(DIFFICULTY + 1, 2147483647 - (DIFFICULTY + 1))
        h = murmurhash3_32(key)
        
        task = {
            "id": i,
            "hash": h,
            "hash_start": key - random.randint(1,DIFFICULTY),
            "hash_end": key + random.randint(1,DIFFICULTY),
            "priority": random.randint(0, 255)
        }
        tasks.append(task)

    with open("c_random_inputs.txt", "w") as f:
        for t in tasks:
            f.write(f"{t['id']} {t['hash']} {t['hash_start']} {t['hash_end']} {t['priority']}\n")

    with open("spin_random_inputs.pml", "w") as f:
        f.write(f"#define MAX_TASKS {MAX_TASKS}\n\n")
        f.write("int task_ids[MAX_TASKS] = {{ {} }};\n".format(
            ", ".join(str(t["id"]) for t in tasks)
        ))
        f.write("int task_hashes[MAX_TASKS] = {{ {} }};\n".format(
            ", ".join(str(t["hash"]) for t in tasks)
        ))
        f.write("int task_hash_starts[MAX_TASKS] = {{ {} }};\n".format(
            ", ".join(str(t["hash_start"]) for t in tasks)
        ))
        f.write("int task_hash_ends[MAX_TASKS] = {{ {} }};\n".format(
            ", ".join(str(t["hash_end"]) for t in tasks)
        ))
        f.write("byte task_priorities[MAX_TASKS] = {{ {} }};\n".format(
            ", ".join(str(t["priority"]) for t in tasks)
        ))


    print("Generated random inputs:", tasks)

if __name__ == "__main__":
    main()