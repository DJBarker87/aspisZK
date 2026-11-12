#!/bin/bash
# Aspis freeze: release-style translator emission of the whole on-chain path of one source tree, in ONE
# fv_slot.sh scope (8 GiB cap, never raised). A tool record: which functions the second tool pair (Charon
# 454586e9, Aeneas 0d21a9ec with -abort-on-error) translates and whether the emitted Lean elaborates against the
# R1 (L187) library. Nothing here is a proof.
# Usage: fv_frz_emit.sh <source-dir-name> <label> <program-feature-list> <verifier-feature-list-for-native>
#   <source-dir-name>  a source tree under the workspace, read only (e.g. src-cand1)
#   <label>            names the output directory frz-emit/<label> and the attempt FRZE-<label>
#   the two feature lists: program crate (deployed set) and verifier crate (its own names, as the verifier worker's
#   TP-C70). Roots, opaque items, the statement and core feature sets, the named gaps and the pass rewrite list are
#   read from the per-tree config frz-emit/config/<source-dir-name>.json; this script names none of them.
# Inside the scope: fv_frz_emit_inner.sh -> fv_frz_emit_run.py (five Charon runs: verifier, program, statement
# semantic side, statement decoders, core; Aeneas release-style on each; completeness, erased-region and defect
# scans; the four Lean modules of each emission compiled one at a time by fv_frz_emit_lean_one.sh; function text
# against the pin; the row table rows.tsv).
# Time is expected in the five cold Charon cargo builds (one target directory per tree and scope), the Aeneas runs
# (up to about two and a half minutes for the verifier crate) and the Funs modules in Lean.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
F=$W/frz-emit
[ $# -eq 4 ] || { echo "usage: fv_frz_emit.sh <source-dir-name> <label> <program-features> <verifier-features>"; exit 2; }
SRC=$1; LABEL=$2
test -d "$W/$SRC" || { echo "no source tree $W/$SRC"; exit 2; }
test -f "$F/config/$SRC.json" || { echo "no config $F/config/$SRC.json"; exit 2; }
test ! -e "$F/$LABEL" || { echo "output exists: $F/$LABEL (use a new label)"; exit 2; }
cd $W
bash fv_slot.sh FRZE-$LABEL 5400 bash $F/bin/fv_frz_emit_inner.sh "$@" > $F/emit-$LABEL.log 2>&1
rc=$?
echo "scope exit $rc"; cat $F/emit-$LABEL.log | tail -2; cat $F/$LABEL/steps.txt 2>/dev/null | cut -c1-300
exit $rc
