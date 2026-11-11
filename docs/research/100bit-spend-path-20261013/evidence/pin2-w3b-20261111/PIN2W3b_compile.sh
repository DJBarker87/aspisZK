#!/bin/zsh
# PIN2 W3b local compile wrapper (copy of the W2 wrapper) (after NPR_compile.sh): one lean process, -M7000,
# -DElab.async=false, 180 s alarm; overlay-PIN2 shadows the L187 objects.
# usage: PIN2_compile.sh <Module path without .lean, e.g. R0P/Core> <note>
set -u
M=$1; NOTE=${2:-}
W=/Users/dominic/ZK/.worktrees/pin2-lean
EV=$W/docs/research/100bit-spend-path-20261013/evidence/pin2-w3b-20261111
C=$HOME/aspis-lead-infra/l187-closure
OV=$C/overlay-PIN2
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
TSV=$EV/PIN2-W3b-COMPILE.tsv
mkdir -p $OV/$(dirname $M) $EV/logs
N=$(( $(ls $EV/logs 2>/dev/null | grep -c '\.log$') + 1 )); ID=$(printf 'PIN2W3b_C%03d' $N)
LOG=$EV/logs/$ID-${M//\//_}.log
pgrep -x lean >/dev/null && { echo "another lean process is running; refusing"; exit 3; }
SRCDIR=${SRCDIR:-$EV/sources}
SHA=$(shasum -a 256 $SRCDIR/$M.lean | cut -d' ' -f1)
REV=$(git -C $W rev-parse HEAD)
( cd $SRCDIR && LEAN_PATH="$OV:$C/objs:$C/base" /usr/bin/time -l perl -e 'alarm 180; exec @ARGV' $LEAN -M7000 -DElab.async=false -o $OV/$M.olean $M.lean ) > $LOG 2>&1
EXIT=$?
WALL=$(grep -E ' real ' $LOG | tail -1 | awk '{print $1}')
RSS=$(grep 'maximum resident set size' $LOG | awk '{print $1}')
AX=$(grep -c "depends on axioms\|does not depend on any axioms" $LOG)
BAD=$(grep "depends on axioms" $LOG | grep -c 'sorryAx\|native\|ofReduceBool\|trustCompiler')
SWAP=$(sysctl -n vm.swapusage | sed 's/.*used = \([^ ]*\).*/\1/')
[ -s $TSV ] || printf 'id\ttarget\texit\twall_s\tmax_rss_bytes\tswap_used_host\tsource_sha256\trevision\taxioms\tnote\n' > $TSV
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s (dirty worktree)\t%s #print axioms lines; %s with sorryAx/other\t%s\n' $ID $M $EXIT "$WALL" "$RSS" "$SWAP" $SHA $REV $AX $BAD "$NOTE" >> $TSV
echo "$ID exit=$EXIT wall=$WALL rss=$RSS axioms=$AX bad=$BAD"
grep -vE "^ *[0-9]+ +[a-z]" $LOG | grep -v "^ *[0-9.]* real" | grep -v "unusedSectionVars\|automatically included\|consider restructuring\|omit \[\|\[DecidableEq K\]\|^ *$\|^Note:" | head -${3:-60}
