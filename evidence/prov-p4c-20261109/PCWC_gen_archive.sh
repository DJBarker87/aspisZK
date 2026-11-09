#!/bin/bash
set -e
cd "$(dirname "$0")"
gen() { # module run ns tag
python3 PCWC_gen_equalities.py --module "$1" --fresh-dir "$2_emitted/raw/$3" --fresh-ns "$3" --gate-source "gatesrc/$4_Funs.lean" --gate-types-source "gatesrc/$4_Types.lean" --partition ../prov-p0-20261109/PCO_PARTITION.json --out "PRVEq_$(echo $1 | tr . _).lean" --report "PRVEq_$(echo $1 | tr . _).report.json" --state-out "PRVEq_$(echo $1 | tr . _).state1.json"
}
gen AspisR1WithdrawalCaller.Funs PCWC_E003 AspisR1WithdrawalCaller WC
gen AspisR1SemanticCallExtraction.Funs PCWC_E004 AspisR1SemanticCallExtraction SC
gen AspisR1BatchedWeightsExtraction.Funs PCWC_E005 AspisR1BatchedWeightsExtraction BW
