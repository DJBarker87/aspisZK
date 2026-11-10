#!/bin/bash
# usage: bash PCWM_ppgen.sh TAG FRESHDIR  -- generator pass for AspisR1PublicPreparation.Types
cd "$(dirname "$0")"
tag=$1; dir=$2; ns=$(grep -m1 "^namespace" $dir/Types.lean | awk '{print $2}')
python3 -B PCWM_gen_equalities.py --module AspisR1PublicPreparation.Types --tag $tag --fresh-dir $dir --fresh-ns $ns --gate-source inputs/gate_AspisR1PublicPreparation_Types.lean --out PRVEq_AspisR1PublicPreparation_Types$tag.lean --report gen/PP$tag.report.json --state-out gen/PP$tag.state.json --prune-fresh 2>&1 | tail -1
