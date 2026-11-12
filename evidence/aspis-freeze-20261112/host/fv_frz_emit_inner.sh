#!/bin/bash
# Runs INSIDE one fv_slot.sh scope (started by fv_frz_emit.sh). See that file.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
F=$W/frz-emit
SRC=$1; LABEL=$2; PF=$3; VF=$4
mkdir -p $F/$LABEL
exec python3 -I $F/bin/fv_frz_emit_run.py "$W/$SRC" "$F/$LABEL" "$F/config/$SRC.json" "$PF" "$VF"
