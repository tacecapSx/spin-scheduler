import json

MAX_TASKS = 4

with open("c_trace.json", "r") as f:
    trace = json.load(f)["events"]

event_count = 0

for i in range(len(trace)):
    for j in range(len(trace[i]["tasks"])):
        event_count += 1

# Write SPIN trail
with open("spin_input_trail.pml", "w") as f:
    f.write(f"#define MAX_TASKS {MAX_TASKS}\n")
    f.write(f"#define TRAIL_COUNT {event_count}\n\n")

    f.write("c_decl { typedef struct { int id; char state; int hash; int hash_start; int hash_end; int hash_progress; char p; } TrailEvent; }\n\n")

    f.write(f"c_code {{ TrailEvent trail_data[{event_count}]; }}\n\n")

    f.write('int trail_index = 0;\n\n')
    
    f.write(f"chan trail = [MAX_TASKS] of {{\nint, //id\nbyte, //state\nint, //hash\nint, //hash_start\nint, //hash_end\nint, //hash_progress\nbyte //p\n}};\n\n")

    f.write("proctype init_trace() {\n")

    event_count = 0
    
    for i in range(len(trace)):
        for j in range(len(trace[i]["tasks"])):
            t = trace[i]["tasks"][j]
            
            f.write("c_code {\n")
            f.write(f"trail_data[{event_count}].id = {t['id']};\n")
            f.write(f"trail_data[{event_count}].state = {t['state']};\n")
            f.write(f"trail_data[{event_count}].hash = {t['hash']};\n")
            f.write(f"trail_data[{event_count}].hash_start = {t['hash_start']};\n")
            f.write(f"trail_data[{event_count}].hash_end = {t['hash_end']};\n")
            f.write(f"trail_data[{event_count}].hash_progress = {t['hash_progress']};\n")
            f.write(f"trail_data[{event_count}].p = {t['priority']};\n")
            f.write("}\n\n")

            event_count += 1
    f.write("}")