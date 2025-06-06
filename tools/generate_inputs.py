import random
import argparse

MAX_TASKS = 4
THREAD_COUNT = 2

# Set up the parser
parser = argparse.ArgumentParser(description="Generate random scheduler inputs with seed, difficulty, and maximum execution time.")

parser.add_argument("--seed", type=int, help="Seed for random number generator. If not provided, uses a random seed.")
parser.add_argument("--difficulty", type=int, default=6, help="Difficulty level. Determines how long a task will maximally take to terminate. (default: 6)")
parser.add_argument("--execution_time_max", type=int, default=12, help="Maximum execution time: An upper bound for all the tasks total execution time together. (default: 12)")

args = parser.parse_args()

# Set the seed
if args.seed is not None:
    SEED = args.seed
    print(f"Generating seeded input for {SEED}.")
else:
    SEED = None
    print("Generating unseeded input.")

random.seed(SEED)

# Get other args
DIFFICULTY = args.difficulty
EXECUTION_TIME_MAX = args.execution_time_max

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

def create_tasks():
    execution_time = 0;
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
    
    # Return tasks and execution time if EXECUTION_TIME_MAX is followed, else try again
    return (tasks, execution_time) if execution_time <= EXECUTION_TIME_MAX else create_tasks()

def generate_ltl_for_priority_scheduling(num_tasks=4):
    ltl = "/*\n  Helper macro: checks a task's entered_running signal, which only triggers once (when its state becomes RUNNING).\n  This is because a lower-priority task is allowed to pre-empt a higher-priority task iff the higher-priority task is RUNNING or TERMINATED,\n  but the higher-priority task may become BLOCKED before the lower-priority one. This case should *not* count as a pre-emption,\n  why we check only exactly when the state changes.\n*/\n"
    ltl += "#define ENTERED_RUNNING(i) \\\n  (task_data[i].entered_running && task_data[i].state == RUNNING)\n\n"
    
    ltl += "// Helper macro: checks if any higher-priority task is still pending (not RUNNING or TERMINATED)\n"
    ltl += "#define HIGHER_PENDING_NOT_ACTIVE(i) \\\n  (\\\n"

    # Generate the macro body
    lines = []
    for j in range(MAX_TASKS):
        lines.append(
            f"    (task_data[{j}].p > task_data[i].p && task_data[{j}].state != RUNNING && task_data[{j}].state != TERMINATED)"
        )
    ltl += " || \\\n".join(lines)
    ltl += " \\\n  )\n\n"

    ltl += "// If task i is RUNNING, no higher-priority task can be pending (i.e. not RUNNING or TERMINATED)\n"
    ltl += "ltl threaded_priority {\n"
    ltl += "  [] (\n"

    conditions = []
    for i in range(MAX_TASKS):
        conditions.append(f"    (ENTERED_RUNNING({i}) -> ! HIGHER_PENDING_NOT_ACTIVE({i}))")
    
    ltl += " &&\n".join(conditions)
    ltl += "\n  )\n}\n"
    
    return ltl

def main():
    tasks, execution_time = create_tasks()

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

        f.write("ltl bounded_and_exact_execution_time {\n")
        f.write("  [] (execution_time <= MAX_EXECUTION_TIME + MAX_TASKS) // + MAX_TASKS because we log the completion as well")
        f.write("\n  &&\n  [] <> (execution_time == MAX_EXECUTION_TIME + MAX_TASKS)\n}\n\n")

        f.write("ltl all_tasks_will_terminate {\n")
        conds = "\n    &&\n    ".join([f"(<> (task_data[{i}].state == TERMINATED))" for i in range(MAX_TASKS)])
        f.write(f"  [] (\n    {conds}\n  )\n}}\n\n")

        f.write("ltl terminated_is_final {\n")
        conds = "\n    &&\n    ".join([f"(task_data[{i}].state == TERMINATED -> [] (task_data[{i}].state == TERMINATED))" for i in range(MAX_TASKS)])
        f.write(f"  [] (\n    {conds}\n  )\n}}\n\n")

        f.write("/*\n  This statement should hopefully *fail*, because we want SPIN to find a counter-example where multi-threading occurs.\n  The reason why we cannot create an \"eventually, multi-threading occurs\" (<>...) claim is that an execution sequence exists where a\n  single thread gets control every time. If this statement *fails*, we effectively prove existential quantification (\"there exists a...\") of multi-threading.\n*/\n")
        f.write("ltl should_fail_single_threaded {\n")
        conds = "\n    + ".join([f"(task_data[{i}].state == RUNNING)" for i in range(MAX_TASKS)])
        f.write(f"  [] (\n    ( {conds} ) <= 1\n  )\n}}\n\n")

        f.write("ltl thread_safety {\n")
        conds = conds = " + ".join([f"in_cs[{i}]" for i in range(THREAD_COUNT)])
        f.write(f"  [] (\n    (( {conds} ) == 0 && !heap_locked)\n    ||\n    (( {conds} ) == 1 && heap_locked)\n  )\n}}\n\n")

        f.write("ltl thread_liveness {\n")
        conds = conds = "\n    &&\n    ".join([f"(waiting[{i}] -> <> in_cs[{i}])" for i in range(THREAD_COUNT)])
        f.write(f"  [] (\n    {conds}\n  )\n}}\n\n")

        f.write(generate_ltl_for_priority_scheduling())
    print("Generated random inputs:", tasks)

if __name__ == "__main__":
    main()