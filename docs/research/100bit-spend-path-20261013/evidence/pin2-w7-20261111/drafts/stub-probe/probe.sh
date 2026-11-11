#!/bin/zsh
# uncredited probe compile into scratch overlay stub/ov
S=/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/w7/stub
C=$HOME/aspis-lead-infra/l187-closure; LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
M=$1
while pgrep -x lean >/dev/null; do sleep 2; done
( cd $S/src && LEAN_PATH="$S/ov:$C/overlay-PIN2-W7:$C/overlay-HOST-P1:$C/overlay-PIN2:$C/objs:$C/base" perl -e 'alarm 180; exec @ARGV' $LEAN -M7000 -DElab.async=false -o $S/ov/$M.olean.tmp $M.lean ) > $S/log-$M.txt 2>&1
E=$?
[ $E = 0 ] && mv $S/ov/$M.olean.tmp $S/ov/$M.olean
echo "$M exit=$E errors=$(grep -c 'error' $S/log-$M.txt)"
exit $E
