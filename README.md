# spin-scheduler
A software project created by Martin Handest for the BSc thesis "Implementing and Formally Verifying a Microkernel-Style OS Scheduler using SPIN", containing the titular micro-kernel style OS scheduler.

## Project Structure
The project consists of two stages: v0 and v1. v1, the fully featured version exists on the `main` branch. The more basic v0 exists in its own branch.

### Tools
Tools for code generation exist in the `tools` folder.

**generate_inputs.py**
Generates a seeded or unseeded set of random inputs for the scheduler and model to produce various execution traces. It also generates a `.pml` source file of LTL statements used by both Promela models. This file is generated because the semantics of the statements change based on the chosen task amount.

**make_spin_trail.py**
Reads `main.c`'s execution trace and converts it into includeable Promela code to be used by tracer.pml.

**verify_all_ltl.sh**
A utility for running a given Promela model using SPIN once for each LTL statement.

### C Scheduler
C source code exists in the `scheduler` folder, and generated files pertaining to the C program are also placed in here.

### Promela Models
Promela models and associated files exist in the `models` folder.


v0 -> v1

1. Single-threaded -> Multi-threaded

2. Non-preemptive -> Preemptive

3. Round-robin scheduling -> Priority-based scheduling

4.	Cooperative task switching -> Message-passing model (interprocess communication)

5.	Only if using priority: Verify liveness/deadlock -> Verify also starvation/load balancing