#!/bin/bash
cd "$(dirname "$0")"
python3 -B PCVR_run.py "$1" extract > "$1.client.log" 2>&1
echo "exit=$?" >> "$1.client.log"
