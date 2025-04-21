# Target name
TARGET = scheduler/main

# Compiler and flags
CC = gcc
CFLAGS = -Wall -O3
LIBS = -pthread

# Directories
SRC_DIR = scheduler
TOOLS_DIR = tools

# Source files
SRC = $(SRC_DIR)/main.c
CSRC = $(SRC_DIR)/heap.c
OBJS = $(SRC:.c=.o) $(CSRC:.c=.o)

# Build target
$(TARGET): $(SRC) $(CSRC)
	$(CC) $(CFLAGS) -o $(TARGET) $(SRC) $(CSRC) $(LIBS)



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