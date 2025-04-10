# Name of the executable
TARGET = main

# Compiler to use
CC = gcc

# Compiler flags (optional)
CFLAGS = -Wall -O3

# Source file
SRC = main.c

# Rule to build the executable
$(TARGET): $(SRC)
	$(CC) $(CFLAGS) -o $(TARGET) $(SRC)

# Rule to clean up generated files
clean:
	rm -f $(TARGET)
