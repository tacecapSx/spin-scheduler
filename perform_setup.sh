#!/bin/bash

python3 generate_inputs.py

make

./main

python3 make_spin_trail.py