#!/bin/bash
# Aspis translatability pass: translate one patched tree and elaborate the result, in ONE fv_slot.sh scope (8 GiB cap).
# Usage: fv_tp1_emit1.sh <tag> <verifier-charon-spec> <program-charon-spec>
# Inside the scope (fv_tp1_emit1_inner.sh), for the verifier crate and then the program crate:
#   Charon (second pair); Aeneas without -abort-on-error (lists every rejection); if it rejects nothing, Aeneas again
#   WITH -abort-on-error (the release-style emission); the completeness and erased-region scan of the LLBC against the
#   emission; the four emitted files adapted (TP_adapt.py, TP_rules_release.json) and compiled one at a time against
#   the R1 (L187) library (fv_lean_one.sh); each Lean error assigned to its declaration (TP_errmap.py).
# Time is expected in Charon's cargo build (one target directory per tree, crate and tool pair), two to three minutes
# per Aeneas run, and the Funs modules in Lean.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
bash fv_slot.sh TP-E$1 5400 bash $W/fv_tp1_emit1_inner.sh "$@" > $W/tp1/emit1-$1.log 2>&1
echo "scope exit $?"; cat $W/tp1/emit1-$1.steps 2>/dev/null | cut -c1-300
