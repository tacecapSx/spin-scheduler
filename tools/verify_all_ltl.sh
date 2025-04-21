#!/bin/bash

# Get the filename from the first argument
filename="$1"

# Check if the filename was actually provided
if [ -z "$filename" ]; then
  echo "Usage: $0 <filename>"
  exit 1
fi

# Check if the file exists AND is a regular file
if [[ ! -f "$filename" ]]; then
  echo "File '$filename' does not exist"
  exit 1
fi

ltl_statements_file="model/ltl_statements.pml"

# Check if the LTL statements file exists
if [[ ! -f "$ltl_statements_file" ]]; then
  echo "LTL statements file '$ltl_statements_file' not found!"
  exit 1
fi

# Extract LTL statement names from the ltl_statements.pml file
ltl_names=$(grep -oP 'ltl \K\w+' "$ltl_statements_file")

# Check if there are any LTL statements
if [[ -z "$ltl_names" ]]; then
  echo "No LTL statements found in '$ltl_statements_file'."
  exit 1
fi

# Loop through all the LTL names and run verification
for ltl_name in $ltl_names; do
  echo "Verifying LTL statement: $ltl_name"
  
  # Run the spin verification command and capture the output
  output=$(spin -search -ltl "$ltl_name" -m100000 "$filename" 2>&1)
  
  # Check if the output contains the phrase indicating failure
  if echo "$output" | grep -q "pan:1"; then
    # If an assertion is violated, print the failure message
    echo "FAILURE: LTL statement $ltl_name failed."
    echo "$output" | grep "pan:"
    echo "---------------------------------------------"
  else
    # If no failure, print success message
    echo "SUCCESS: LTL statement $ltl_name passed."
    echo "---------------------------------------------"
  fi
done

echo "Verification complete."
