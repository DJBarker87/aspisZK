#!/bin/zsh
# Rescan the object import lists of the writable/growing layers (overlay-PIN2-W4 and
# overlay-HOST-P1) with Imports.lean (readModuleData).  usage: PIN2W6_rescan.sh <scan_dir>
S=$1; C=$HOME/aspis-lead-infra/l187-closure
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
T=$(dirname $0)
for d in overlay-PIN2-W4 overlay-HOST-P1; do
  (cd $C/$d && find . -name '*.olean' | sed 's|^\./||' | sort > $S/list-$d.txt)
  while pgrep -x lean >/dev/null; do sleep 2; done
  $LEAN --run $T/Imports.lean $C/$d $S/list-$d.txt $S/imp-$d.tsv
  echo "$d $(wc -l < $S/imp-$d.tsv)"
done
