#!/bin/bash

python3 generate_inputs.py

gcc main.c -o main

./main

python3 make_spin_trail.py

spin -a main.pml

gcc pan.c -o pan