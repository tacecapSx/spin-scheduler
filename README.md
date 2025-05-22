# spin-scheduler
A software project created by Martin Handest for the BSc thesis "Implementing and Formally Verifying a Microkernel-Style OS Scheduler using SPIN", containing the titular micro-kernel style OS scheduler.

## Setup
First, make sure you are running an operating system that supports POSIX threads (pthreads). Any Linux machine will do. To run the scheduler and model checking, clone the repository:

```
git clone https://github.com/tacecapSx/spin-scheduler.git
```

Then, the tools can be used manually (for example, the seed of `generate_inputs.py` can be changed) or, you can simply run:

```
make setup
```

This `make` flag will automatically generate random inputs, compile the C source code, execute it, and utilize the C scheduler's execution trace to make input for `tracer.pml`. Finally, to verify multiple LTL properties easily, the tool `verify_all_ltl.sh` is included and can be called on one of the models:

```
./verify_all_ltl.sh model/main.pml
```

Of course, SPIN commands can be executed on the models at the user's leisure at this point (after inputs have been generated, and an execution trace has been created for `tracer.pml`).

## Project Structure
The project consists of two stages: v0 and v1. v1, the fully featured version exists on the `main` branch. The more basic v0 exists in its own branch.

![Diagram](https://github.com/user-attachments/assets/0097cb20-a981-4500-8679-88b16bb42716)

### Tools
Tools for code generation exist in the `tools` folder.

#### generate_inputs.py
Generates a seeded or unseeded set of random inputs for the scheduler and model to produce various execution traces. It also generates a `.pml` source file of LTL statements used by both Promela models. This file is generated because the semantics of the statements change based on the chosen task amount.

#### make_spin_trail.py
Reads `main.c`'s execution trace and converts it into includeable Promela code to be used by `tracer.pml`.

#### verify_all_ltl.sh
A utility for running a given Promela model using SPIN once for each LTL statement.

### C Scheduler
C source code exists in the `scheduler` folder, and generated files pertaining to the C program are also placed in here.

### Promela Models
Promela models and associated files exist in the `model` folder.

#### main.pml
This is the *"mimic"* model as described in the thesis, designed to align with the behavior of the C implementation as closely as possible.

#### tracer.pml
This is the *"tracer"* model as described in the thesis, designed to take an execution trace (of the C program) as input to re-trace it in a formally verifiable environment.

## Version Differences
The scheduler and associated models are developed in two versions: v0 and v1. Following are explanations of both.

### v0
Found in the `v0` branch, v0 is a baseline implementation executing tasks in a single-threaded, concurrency-free environment. It employs a naive round-robin approach, not considering task priorities at all. Liveness and deadlock-freedom are the key properties verified. This version serves as a jumping-off point for v1, the full implementation.

### v1
Found in the `main` branch, v1 is the full implementation featuring a dynamic round-robin scheduling algorithm accounting for priorities. Tasks are executed concurrently by a thread pool. These properties are reflected in the Promela models as well, allowing for priority inversion and concurrency checks.

v0 -> v1

1. Single-threaded -> Multi-threaded

2. Non-preemptive -> Preemptive

3. Round-robin scheduling -> Priority-based scheduling

4.	Cooperative task switching -> Message-passing model (interprocess communication)

5.	Only if using priority: Verify liveness/deadlock -> Verify also starvation/load balancing