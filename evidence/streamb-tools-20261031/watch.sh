#!/bin/bash
# exits when any listed job output gains codex-exit= (DONE), or when a job looks dead
# (no process for its worktree and its newest output file idle > 3600 s: DEAD), or after $1 seconds (HEARTBEAT)
S=/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad; lim=$1; shift; t=0
while [ $t -lt $lim ]; do
  for n in "$@"; do
    grep -q codex-exit= $S/codex-$n.out 2>/dev/null && { echo "DONE $n"; exit 0; }
    f=$(ls -t $S/codex-$n.out* 2>/dev/null | head -1)
    if [ -n "$f" ]; then
      idle=$(( $(date +%s) - $(stat -f %m "$f") ))
      if [ $idle -gt 3600 ]; then echo "IDLE $n (no output 1h; check process)"; exit 0; fi
    fi
  done
  sleep 60; t=$((t+60))
done; echo HEARTBEAT
