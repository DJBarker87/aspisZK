cd "$(dirname "$0")"
ing() { # module run ns gatefile
F=$(echo $1 | tr . _)
python3 PCWE_gen_equalities.py --module "$1" --fresh-dir "$2_emitted/raw/$3" --fresh-ns "$3" --gate-source "gatesrc/$4" --partition ../prov-p0-20261109/PCO_PARTITION.json --out "PRVEq_$F.lean" --report "PRVEq_$F.report.json" --state "PRVEq_$F.state1.json" --state-out "PRVEq_$F.state2.json" --lean-log PCWE_L007.lean.log --bundle-offsets bundle_T1_offsets.json | tail -1
}
ing AspisR1AdapterReconstruct.Types PCWE_E003 AspisR1AdapterReconstruct AD_Types.lean
ing AspisR1PrefixAggregateParser.Types PCWE_E001 AspisR1PrefixAggregateParser PR_Types.lean
ing AspisR1CircleSampleWrapper.Types PCWE_E004 AspisR1CircleSampleWrapper CI_Types.lean
