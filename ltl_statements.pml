ltl p1 {[] (task_count <= MAX_TASKS)}
ltl p2 {<> (task_count == 0)}
ltl p3 {(<> (task_queue[0].state == TERMINATED)) || ([] (task_count == 0))}
ltl will_fail {[] (task_count < 2)}