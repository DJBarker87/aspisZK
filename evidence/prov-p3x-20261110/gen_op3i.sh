cd "$(dirname "$0")"
python3 -B PCWF_gen_equalities.py --module Op3I_Source --kind funs \
 --fresh-dir ../prov-p2j-20261110/PCUJ_E003_emitted/raw/NJS_Extract --fresh-ns NJS_Extract \
 --gate-source inputs/gate_Op3I_Source_merged.lean --gate-types-source inputs/gate_Op3I_Source_merged.lean \
 --only inputs/only_op3i.json --prune-fresh --out PRVEq_Op3I_Source_g1.lean --report gen/op3i_g1.report.json --state-out gen/op3i_g1.state.json 2>&1 | tail -8
rm -rf __pycache__
