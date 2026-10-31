#!/bin/bash
# usage: waitjob.sh <name>; exits when the job's out file has its final codex-exit line
O=/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/codex-$1.out
until [ -f "$O" ] && tail -1 "$O" | grep -q '^codex-exit='; do sleep 60; done; echo "DONE $1 $(tail -1 $O)"
