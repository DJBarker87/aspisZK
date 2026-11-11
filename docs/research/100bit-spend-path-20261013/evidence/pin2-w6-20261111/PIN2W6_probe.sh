#!/bin/zsh
# Uncredited probe compile (iteration on a draft): same toolchain, flags, alarm and
# LEAN_PATH as PIN2W6_compile.sh, but the object goes to the scratchpad, never an
# overlay.  Logged in probes/.  usage: PIN2W6_probe.sh <dir> <Module>
set -u
D=$1; M=$2
EV=/Users/dominic/ZK/.worktrees/pin2-lean/docs/research/100bit-spend-path-20261013/evidence/pin2-w6-20261111
C=$HOME/aspis-lead-infra/l187-closure
OUT=/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/w6probe
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
mkdir -p $EV/probes $OUT
N=$(( $(ls $EV/probes | grep -c '\.log$') + 1 )); LOG=$EV/probes/$(printf 'P%03d' $N)-$M.log
shasum -a 256 $D/$M.lean > $LOG
while pgrep -x lean >/dev/null; do sleep 2; done
( cd $D && LEAN_PATH="$C/overlay-PIN2-W4:$C/overlay-PIN2:$C/overlay-HOST-P1:$C/objs:$C/base" /usr/bin/time -l perl -e 'alarm 180; exec @ARGV' $LEAN -M7000 -DElab.async=false -o $OUT/$M.olean $M.lean ) >> $LOG 2>&1
E=$?; echo "probe $LOG exit=$E"; grep -E 'error|warning: declaration uses|depends on axioms' $LOG | head -30; grep -E 'real|maximum resident' $LOG
