cd "$(dirname "$0")"
gent() { # module run ns gatefile tag
python3 PCWE_gen_equalities.py --module "$1" --fresh-dir "$2_emitted/raw/$3" --fresh-ns "$3" --gate-source "gatesrc/$4" --partition ../prov-p0-20261109/PCO_PARTITION.json --out "PRVEq_$(echo $1 | tr . _).lean" --report "PRVEq_$(echo $1 | tr . _).report.json" --state-out "PRVEq_$(echo $1 | tr . _).state1.json" | tail -1
}
gent AspisR1AdapterReconstruct.Types PCWE_E003 AspisR1AdapterReconstruct AD_Types.lean
gent AspisR1PrefixAggregateParser.Types PCWE_E001 AspisR1PrefixAggregateParser PR_Types.lean
gent AspisR1CircleSampleWrapper.Types PCWE_E004 AspisR1CircleSampleWrapper CI_Types.lean
