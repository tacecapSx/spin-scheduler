import random
import struct

MAX_TASKS = 4
SEED = 90024
DIFFICULTY = 100

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
    with open("c_random_inputs.txt", "w") as f:
        for t in tasks:
            f.write(f"{t['id']} {t['hash']} {t['hash_start']} {t['hash_end']} {t['priority']}\n")

    # Generate SPIN inputs
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

    # Generate LTL statements
    with open("ltl_statements.pml", "w") as f:
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
        
        f.write("ltl round_robin {\n")
        for i in range(MAX_TASKS):
            next_id = (i+1) % MAX_TASKS
            other_ids = [j for j in range(MAX_TASKS) if j not in [i, next_id]]
            
            f.write(f"  [] (\n    (task_queue[{i}].state == RUNNING) -> (\n")
            f.write(f"      (!task_queue[{next_id}].state == TERMINATED) -> (\n")
            f.write(f"        ({' && '.join([f'task_queue[{j}].state != RUNNING' for j in other_ids])})")
            f.write(f" U (task_queue[{next_id}].state == RUNNING)\n      )\n    )\n  )\n")
            f.write("  &&\n" if i != MAX_TASKS - 1 else "}\n")
            
            '''f.write(f"  [] ( (task_queue[{i}].state == RUNNING) -> \n")
            f.write(f"    (({' && '.join([f'(task_queue[{j}].state != RUNNING)' for j in other_ids])}) U (task_queue[{(i+1) % MAX_TASKS}].state == RUNNING)) )\n")
            f.write("  &&\n" if i != MAX_TASKS - 1 else "}\n")'''
            
            '''f.write(f"  []( (task_queue[{i}].state == RUNNING) -> (\n")
            
            conditions = []

            for offset in range(1, MAX_TASKS+1):
                j = (i + offset) % MAX_TASKS

                # Get all tasks between i and j that must be TERMINATED
                terminated_indices = [(i + k) % MAX_TASKS for k in range(1, offset)]

                # Build the condition to ensure intermediate tasks are TERMINATED
                termination_check = " && ".join(
                    f"(task_queue[{idx}].state == TERMINATED)" for idx in terminated_indices
                )

                # Build the forbidden clause: all other tasks (excluding i, j, and terminated) must not be RUNNING
                forbidden_clause = " && ".join(
                    f"(task_queue[{k}].state != RUNNING)"
                    for k in range(MAX_TASKS)
                    if k not in {i, j, *terminated_indices}
                )
                    
                # Add the condition
                if offset == MAX_TASKS: # Last condition
                    condition = f"( {termination_check} )"
                elif not termination_check: # No termination check yet
                    condition = f"( ( {forbidden_clause} ) U (task_queue[{j}].state == RUNNING) )"
                elif forbidden_clause: # Forbidden other tasks exist
                    condition = f"( ({termination_check}) -> ( {forbidden_clause} ) U (task_queue[{j}].state == RUNNING) )"
                else:
                    condition = f"( ({termination_check}) -> <> (task_queue[{j}].state == RUNNING) )"
                conditions.append(condition)
            
            # Add "all others are terminated" condition
            # = ' && '.join([])
            #conditions.append(f"( {others_terminated_clause} )")

            # Join all conditions with ||
            f.write("    " + "\n    ||\n    ".join(conditions) + "\n")
            f.write("  ))")

            # Full formula
            f.write(" &&\n" if i < MAX_TASKS - 1 else "\n}\n")'''




    print("Generated random inputs:", tasks)

if __name__ == "__main__":
    main()