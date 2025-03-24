import random

SEED = 4883
random.seed(SEED)

MAX_TASKS = 4

tasks = []
for i in range(MAX_TASKS):
    task = {
        "id": i,
        "burst_time": random.randint(1, 500),
        "priority": random.randint(0, 255)
    }
    tasks.append(task)

with open("c_random_inputs.txt", "w") as f:
    for t in tasks:
        f.write(f"{t['id']} {t['burst_time']} {t['priority']}\n")

with open("spin_random_inputs.pml", "w") as f:
    f.write(f"#define MAX_TASKS {MAX_TASKS}\n\n")
    f.write("int task_ids[MAX_TASKS] = {{ {} }};\n".format(
        ", ".join(str(t["id"]) for t in tasks)
    ))
    f.write("int task_burst_times[MAX_TASKS] = {{ {} }};\n".format(
        ", ".join(str(t["burst_time"]) for t in tasks)
    ))
    f.write("byte task_priorities[MAX_TASKS] = {{ {} }};\n".format(
        ", ".join(str(t["priority"]) for t in tasks)
    ))


print("Generated random inputs:", tasks)
