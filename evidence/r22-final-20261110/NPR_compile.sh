#!/bin/zsh
# NPR_ local compile wrapper: one lean process, -M7000, 180 s wall cap; appends one row to NPR_COMPILE.tsv.
# usage: NPR_compile.sh <Module> <note>
set -u
M=$1; NOTE=${2:-}
EV=/Users/dominic/ZK/.worktrees/cx-r22l/evidence/r22-final-20261110
C=$HOME/aspis-lead-infra/l187-closure
OV=$C/overlay-NPR
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
mkdir -p $OV $EV/NPR_logs
N=$(( $(ls $EV/NPR_logs 2>/dev/null | grep -c '\.log$') + 1 )); ID=$(printf 'NPR_C%03d' $N)
LOG=$EV/NPR_logs/$ID-$M.log
pgrep -x lean >/dev/null && { echo "another lean process is running; refusing"; exit 3; }
SHA=$(shasum -a 256 $EV/$M.lean | cut -d' ' -f1)
REV=$(git -C /Users/dominic/ZK/.worktrees/cx-r22l rev-parse HEAD)
START=$(date +%s.%N 2>/dev/null || python3 -c 'import time;print(time.time())')
( LEAN_PATH="$C/objs:$C/base:$C/overlay-NPH:$OV" /usr/bin/time -l perl -e 'alarm 180; exec @ARGV' $LEAN -M7000 -DElab.async=false -o $OV/$M.olean $EV/$M.lean ) > $LOG 2>&1
EXIT=$?
WALL=$(grep -E 'real' $LOG | tail -1 | awk '{print $1}')
RSS=$(grep 'maximum resident set size' $LOG | awk '{print $1}')
AX=$(grep -c "depends on axioms\|does not depend on any axioms" $LOG)
BAD=$(grep "depends on axioms" $LOG | grep -c 'sorryAx\|native\|ofReduceBool\|trustCompiler')
SWAP=$(sysctl -n vm.swapusage | sed 's/.*used = \([^ ]*\).*/\1/')
[ -s $EV/NPR_COMPILE.tsv ] || printf 'id\ttarget\texit\twall_s\tmax_rss_bytes\tswap_used_host\tsource_sha256\trevision\taxioms\tnote\n' > $EV/NPR_COMPILE.tsv
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s (dirty worktree)\t%s #print axioms lines; %s with sorryAx/other\t%s\n' $ID $M $EXIT "$WALL" "$RSS" "$SWAP" $SHA $REV $AX $BAD "$NOTE" >> $EV/NPR_COMPILE.tsv
echo "$ID exit=$EXIT wall=$WALL rss=$RSS axioms=$AX bad=$BAD"
grep -vE '^ *[0-9]+ +[a-z]' $LOG | head -${3:-80}
