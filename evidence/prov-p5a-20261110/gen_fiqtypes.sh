cd "$(dirname "$0")"
python3 -B PCWJ_gen_equalities.py --module RPu_FIq_NativeTypes --tag=_t2 --fresh-dir inputs/fresh_E015 --fresh-ns PCQG_aspis_statement_sem_c_eo \
 --gate-source inputs/gate_RPu_FIq_NativeTypes.lean --rename-fresh aspis_core.field.M31=field.M31 --rename-fresh aspis_core.= --rename-fresh aspis_statement.= \
 --prune-fresh --out PRVEq_RPu_FIq_NativeTypes_t2.lean --report gen/fiqtypes_t2.report.json --state-out gen/fiqtypes_t2.state.json 2>&1 | tail -8 | cut -c1-600
rm -rf __pycache__
