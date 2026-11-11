#!/bin/zsh
# wait (max 30 min) for any other lean process, then run the W3b wrapper
W=/Users/dominic/ZK/.worktrees/pin2-lean/docs/research/100bit-spend-path-20261013/evidence/pin2-w3b-20261111
for i in {1..900}; do pgrep -x lean >/dev/null || break; sleep 2; done
SRCDIR=${SRCDIR:-$W/sources} $W/PIN2W3b_compile.sh "$@"
