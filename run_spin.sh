#!/bin/bash

spin main.pml > spin_trace.json

# Trim everything before the first '{'
sed -i '0,/{/s/^[^{]*//' spin_trace.json

# Trim everything after the last '}'
sed -i ':a;N;$!ba;s/}[^}]*$/}/' spin_trace.json

echo "Done."