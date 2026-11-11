#!/bin/bash
# usage: bash PCXS_pin2_s1.sh [PIN] [HEAD]
set -e
cd "$(dirname "$0")"
python3 -I PCXS_pin2_s1_gate.py "${1:-c7593d23fdc}" "${2:-d7142292c48}" PIN2_ARTEFACT_GATE
