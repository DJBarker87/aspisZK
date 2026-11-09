#!/bin/bash
# usage: bash run1.sh SPEC RUN [overflow]
export PCQ_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p1a-20261109
[ "$3" = "1" ] && export PCQ_OVERFLOW=1
cd "$(dirname "$0")"
python3 PCQ_render_spec.py "$1" "$2" >/dev/null || exit 3
timeout 900 python3 PCQ_run.py "$2" extract > "$2.client.log" 2>&1
echo "$2 $1 overflow=${3:-0} rc=$?" >> chain.log
