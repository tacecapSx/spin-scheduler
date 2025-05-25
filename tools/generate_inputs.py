import random
import argparse

MAX_TASKS = 4

# Set up the parser
parser = argparse.ArgumentParser(description="Generate random scheduler inputs with seed, difficulty, and maximum execution time.")

parser.add_argument("--seed", type=int, help="Seed for random number generator. If not provided, uses a random seed.")
parser.add_argument("--difficulty", type=int, default=100, help="Difficulty level. Determines how long a task will maximally take to terminate. (default: 100)")

args = parser.parse_args()

# Set the seed
if args.seed is not None:
    SEED = args.seed
    print(f"Generating seeded input for {SEED}.")
else:
    SEED = None
    print("Generating unseeded input.")

random.seed(SEED)

# Get difficulty
DIFFICULTY = args.difficulty

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
    execution_time = 0

    tasks = []
    for i in range(MAX_TASKS):
        key = random.randint(DIFFICULTY + 1, 2147483647 - (DIFFICULTY + 1))
        h = murmurhash3_32(key)

        e = random.randint(1,DIFFICULTY)
        execution_time += e

        task = {
            "id": i,
            "hash": h,
            "hash_start": key - e,
            "hash_end": key + random.randint(1,DIFFICULTY),
            "priority": random.randint(0, 255)
        }
        tasks.append(task)

    # Generate C inputs
    with open("scheduler/scheduler_random_inputs.txt", "w") as f:
        for t in tasks:
            f.write(f"{t['id']} {t['hash']} {t['hash_start']} {t['hash_end']} {t['priority']}\n")

    # Generate SPIN inputs
    with open("model/spin_random_inputs.pml", "w") as f:
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

    # Generate LTL statements
    with open("model/ltl_statements.pml", "w") as f:
        # Headers
        f.write(f"#define MAX_EXECUTION_TIME {execution_time}\n\n")

        # Statements
        f.write("ltl bounded_and_exact_execution_time {\n  [] (execution_time <= MAX_EXECUTION_TIME + MAX_TASKS) // + MAX_TASKS because we log the completion as well \n  &&\n  [] <> (execution_time == MAX_EXECUTION_TIME + MAX_TASKS)\n}\n")
        f.write("ltl task_count_will_become_zero_and_be_bounded {\n  [] (task_count <= MAX_TASKS)\n  &&\n  [] <> (task_count == 0)\n}\n")

        f.write("ltl all_tasks_will_terminate {\n")
        for i in range(MAX_TASKS):
            f.write(f"  ([] <> (task_data[{i}].state == TERMINATED))\n")

            if i < MAX_TASKS - 1:
                f.write("    &&\n")
            else:
                f.write("  }\n")

        f.write("ltl terminated_is_final {\n  [](\n")
        for i in range(MAX_TASKS):
            f.write(f"    (task_data[{i}].state == TERMINATED -> [](task_data[{i}].state == TERMINATED))\n")

            if i < MAX_TASKS - 1:
                f.write("    &&\n")
            else:
                f.write("  )\n}\n")

        f.write("ltl single_threaded {\n")
        f.write(f"  [] (\n    ( {'\n    + '.join([f'(task_data[{i}].state == RUNNING)' for i in range(MAX_TASKS)])}) <= 1\n  )\n}}\n")
        
        f.write("ltl round_robin {\n")
        for i in range(MAX_TASKS):
            next_id = (i+1) % MAX_TASKS
            other_ids = [j for j in range(MAX_TASKS) if j not in [i, next_id]]
            
            f.write(f"  [] (\n    (task_queue[{i}].state == RUNNING) -> (\n")
            f.write(f"      (!task_queue[{next_id}].state == TERMINATED) -> (\n")
            f.write(f"        ({' && '.join([f'task_queue[{j}].state != RUNNING' for j in other_ids])})")
            f.write(f" U (task_queue[{next_id}].state == RUNNING)\n      )\n    )\n  )\n")
            f.write("  &&\n" if i != MAX_TASKS - 1 else "}\n")

    print("Generated random inputs:", tasks)

if __name__ == "__main__":
    main()