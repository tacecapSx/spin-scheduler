#!/usr/bin/env python3

import re
import sys
import json

class Event:
    def __init__(self, task_count, tasks):
        self.task_count = task_count
        self.tasks = tasks

    def __str__(self):
        return f"STATE: task_count={self.task_count}, tasks={(self.tasks)}"

    def __eq__(self, other):
        # Compare task counts
        if self.task_count != other.task_count:
            return False
        
        # Compare tasks
        for self_task, other_task in zip(self.tasks, other.tasks):
            if (self_task["position"] != other_task["position"] or 
                self_task["id"] != other_task["id"] or 
                self_task["state"] != other_task["state"] or 
                self_task["hash"] != other_task["hash"] or 
                self_task["hash_progress"] != other_task["hash_progress"] or 
                self_task["hash_start"] != other_task["hash_start"] or 
                self_task["hash_end"] != other_task["hash_end"] or 
                self_task["priority"] != other_task["priority"]):
                return False
        
        return True

def parse_trace_file(file_path):
    with open(file_path, "r") as f:
        trace = json.load(f)

    return [Event(e["task_count"], e["tasks"]) for e in trace["events"]]

def compare_traces(c_trace_file, promela_trace_file):
    """Compare C and Promela execution traces."""
    print(f"Comparing traces: '{c_trace_file}' vs '{promela_trace_file}'")
    
    c_events = parse_trace_file(c_trace_file)
    promela_events = parse_trace_file(promela_trace_file)
    
    print(f"C trace has {len(c_events)} events")
    print(f"Promela trace has {len(promela_events)} events")
    
    # Compare trace lengths
    if len(c_events) != len(promela_events):
        print(f"ERROR: Traces have different numbers of events")
        return 1
    
    max_len = min(len(c_events), len(promela_events))
    mismatches = 0
    
    print("\nComparing events:")
    for i in range(max_len):
        c_event = c_events[i]
        p_event = promela_events[i]
        
        if c_event == p_event:
            print(f"Event {i}: MATCH ✓ - {c_event}")
        else:
            mismatches += 1
            print(f"Event {i}: MISMATCH ✗")
            print(f"  C:      {c_event}")
            print(f"  Promela: {p_event}")
    
    # Print summary
    print(f"\nTotal events compared: {max_len}")
    print(f"Total mismatches: {mismatches}")
    
    if mismatches == 0:
        print("VERIFICATION SUCCESSFUL: C implementation matches Promela model")
        return True
    else:
        print("VERIFICATION FAILED: C implementation differs from Promela model")
        return False

def main():
    c_trace_file = "c_trace.json"
    promela_trace_file = "spin_trace.json"
    
    success = compare_traces(c_trace_file, promela_trace_file)
    sys.exit(0 if success else 1)
# Additional statistics
    print("\nStatistics:")
    
    # Count event types
    c_event_types = {}
    p_event_types = {}
    
    for event in c_events:
        event_type = event.event_type
        c_event_types[event_type] = c_event_types.get(event_type, 0) + 1
    
    for event in promela_events:
        event_type = event.event_type
        p_event_types[event_type] = p_event_types.get(event_type, 0) + 1
    
    print("C event counts:")
    for event_type, count in c_event_types.items():
        print(f"  {event_type.name}: {count}")
    
    print("Promela event counts:")
    for event_type, count in p_event_types.items():
        print(f"  {event_type.name}: {count}")


if __name__ == "__main__":
    main()