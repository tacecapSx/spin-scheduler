import json

MAX_TASKS = 4

with open("c_trace.json", "r") as f:
    trace = json.load(f)["events"]

event_count = len(trace)

# Write SPIN trail
with open("spin_input_trail.pml", "w") as f:
    f.write(f"#define MAX_TASKS {MAX_TASKS}\n")
    f.write(f"#define TRAIL_COUNT {event_count}\n\n")

    f.write("c_decl { typedef struct { int queue_position; int id; char state; int hash; int hash_start; int hash_end; int hash_progress; char p; } TrailEvent; }\n\n")

    f.write(f"c_code {{ TrailEvent trail_data[{event_count}]; }}\n\n")

    f.write('int trail_index = 0;\n\n')
    
    f.write(f"chan trail = [2] of {{\nint, //queue_position\nint, //id\nbyte, //state\nint, //hash\nint, //hash_start\nint, //hash_end\nint, //hash_progress\nbyte //p\n}};\n\n")

    f.write("chan go_signal = [1] of {bool};\n\n")

    f.write("proctype init_trace() {\n")
    
    for i in range(len(trace)):
        t = trace[i]
        
        f.write("  c_code {\n")
        f.write(f"    trail_data[{i}].queue_position = {t['queue_position']};\n")
        f.write(f"    trail_data[{i}].id = {t['id']};\n")
        f.write(f"    trail_data[{i}].state = {t['state']};\n")
        f.write(f"    trail_data[{i}].hash = {t['hash']};\n")
        f.write(f"    trail_data[{i}].hash_start = {t['hash_start']};\n")
        f.write(f"    trail_data[{i}].hash_end = {t['hash_end']};\n")
        f.write(f"    trail_data[{i}].hash_progress = {t['hash_progress']};\n")
        f.write(f"    trail_data[{i}].p = {t['priority']};\n")
        f.write("  }\n\n")
    f.write("  go_signal!true;\n}")