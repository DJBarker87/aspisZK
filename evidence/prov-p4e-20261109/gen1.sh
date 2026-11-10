cd "$(dirname "$0")"
gen() { # module run ns tag
python3 PCWE_gen_equalities.py --module "$1" --fresh-dir "$2_emitted/raw/$3" --fresh-ns "$3" --gate-source "gatesrc/$4_Funs.lean" --gate-types-source "gatesrc/$4_Types.lean" --partition ../prov-p0-20261109/PCO_PARTITION.json --out "PRVEq_$(echo $1 | tr . _).lean" --report "PRVEq_$(echo $1 | tr . _).report.json" --state-out "PRVEq_$(echo $1 | tr . _).state1.json" | tail -2
}
gen AspisR1AdapterReconstruct.Funs PCWE_E003 AspisR1AdapterReconstruct AD
gen AspisR1PrefixAggregateParser.Funs PCWE_E001 AspisR1PrefixAggregateParser PR
