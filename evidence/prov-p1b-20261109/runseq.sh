#!/bin/bash
# usage: runseq.sh SID:RUN ...   (sequential; stops at first failure)
export PCQ_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p1b-20261109
cd "$(dirname "$0")"
for x in "$@"; do s=${x%%:*}; r=${x##*:}
 python3 PCQ_render_spec.py $s $r >/dev/null && python3 PCQ_run.py $r extract > run${r#PCQ_E}.out 2>&1 || { echo "FAIL $r"; exit 1; }
done
