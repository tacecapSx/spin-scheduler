# Target name
TARGET = scheduler/main

# Compiler and flags
CC = gcc
CFLAGS = -Wall -O3

# Directories
SRC_DIR = scheduler
TOOLS_DIR = tools

# Source files
SRC = $(SRC_DIR)/main.c
OBJS = $(SRC:.c=.o) $(CSRC:.c=.o)

# Build target
$(TARGET): $(SRC)
	$(CC) $(CFLAGS) -o $(TARGET) $(SRC)



# Setup rule (calls Python + builds + runs)
setup: generate $(TARGET)
	./$(TARGET)
	python3 $(TOOLS_DIR)/make_spin_trail.py

# Python input generator
generate:
	python3 $(TOOLS_DIR)/generate_inputs.py

# Clean up
clean:
	rm -f $(TARGET) $(SRC_DIR)/*.o