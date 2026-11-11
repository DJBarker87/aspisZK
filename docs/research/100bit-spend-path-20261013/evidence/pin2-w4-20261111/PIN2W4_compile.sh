#!/bin/zsh
# PIN2 W4 local compile wrapper (after W3c's PIN2W3c_compile.sh): one lean
# process (waits while any lean runs), -M7000, -DElab.async=false, 180 s alarm.
# LEAN_PATH = overlay-PIN2-W4 : overlay-PIN2 : objs : base.  The separate W4
# overlay holds the PIN2-fixture objects so that the release fixture data in
# objs is not shadowed for other workers until the fixture swap is complete.
# Objects are written through a temporary file and renamed; links refused.
# usage: PIN2W4_compile.sh <Module> <note>   (SRCDIR env = source root; default sources/)
set -u
M=$1; NOTE=${2:-}
W=/Users/dominic/ZK/.worktrees/pin2-lean
EV=$W/docs/research/100bit-spend-path-20261013/evidence/pin2-w4-20261111
C=$HOME/aspis-lead-infra/l187-closure
OV=$C/overlay-PIN2-W4
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
TSV=$W/PIN2-W4-COMPILE.tsv
[ -L $OV/$M.olean ] && { echo "REFUSE: $OV/$M.olean is a symlink"; exit 4; }
mkdir -p $EV/logs
N=$(( $(ls $EV/logs 2>/dev/null | grep -c '\.log$') + 1 )); ID=$(printf 'PIN2W4_C%04d' $N)
LOG=$EV/logs/$ID-$M.log
SRCDIR=${SRCDIR:-$EV/sources}
SHA=$(shasum -a 256 $SRCDIR/$M.lean | cut -d' ' -f1)
REV=$(git -C $W rev-parse HEAD)
BEFORE=$( [ -f $OV/$M.olean ] && shasum -a 256 $OV/$M.olean | cut -c1-16 || echo absent )
while pgrep -x lean >/dev/null; do sleep 2; done
( cd $SRCDIR && LEAN_PATH="$OV:$C/overlay-PIN2:$C/objs:$C/base" /usr/bin/time -l perl -e 'alarm 180; exec @ARGV' $LEAN -M7000 -DElab.async=false -o $OV/$M.olean.tmp $M.lean ) > $LOG 2>&1
EXIT=$?
if [ $EXIT = 0 ]; then mv $OV/$M.olean.tmp $OV/$M.olean; else rm -f $OV/$M.olean.tmp; fi
AFTER=$( [ -f $OV/$M.olean ] && shasum -a 256 $OV/$M.olean | cut -c1-16 || echo absent )
WALL=$(grep -E ' real ' $LOG | tail -1 | awk '{print $1}')
RSS=$(grep 'maximum resident set size' $LOG | awk '{print $1}')
AX=$(grep -c "depends on axioms\|does not depend on any axioms" $LOG)
# every axioms line must name only the three standard axioms
BAD=$(grep "depends on axioms" $LOG | sed 's/.*depends on axioms: *//' | tr -d '[]' | tr ',' '\n' | sed 's/^ *//;s/ *$//' | grep -v -x -e propext -e Classical.choice -e Quot.sound -e '' | wc -l | tr -d ' ')
SORRY=$(grep -c "declaration uses 'sorry'" $LOG)
[ $EXIT = 0 ] && [ "$BAD$SORRY" != "00" ] && EXIT=99
[ -s $TSV ] || printf 'id\ttarget\texit\twall_s\tmax_rss_bytes\tsource_sha256\trevision\taxioms\tolean_before16\tolean_after16\tnote\n' > $TSV
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s #print axioms lines; %s non-standard; %s sorry\t%s\t%s\t%s\n' $ID $M $EXIT "$WALL" "$RSS" $SHA $REV $AX $BAD $SORRY $BEFORE $AFTER "$NOTE" >> $TSV
echo "$ID $M exit=$EXIT wall=$WALL rss=$RSS axioms=$AX bad=$BAD sorry=$SORRY"
[ $EXIT = 0 ] || grep -E "error" -A6 $LOG | head -40
exit $EXIT
