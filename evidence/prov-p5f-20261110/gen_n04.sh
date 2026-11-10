cd "$(dirname "$0")"
F=PCWP_E002_emitted/raw/PCWP_sop2
python3 -B PCWP_gen_equalities.py --module RPu_FIq_Native04 --fresh-dir $F --fresh-ns PCWP_sop2 \
 --gate-source inputs/RPu_FIq_Native04.lean --gate-types-source inputs/RPu_FIq_Native04.lean \
 --rename-fresh aspis_core.= --rename-fresh aspis_statement.= --kind funs \
 --only inputs/only_n04.json --fresh-prelude inputs/hmd_prelude.lean --tag _n04 \
 --gate-extra-source inputs/RPu_FIq_Native01.lean --gate-extra-source inputs/RPu_FIq_Native02.lean --gate-extra-source inputs/RPu_FIq_Native03.lean --prune-fresh --out PRVEq_RPu_FIq_Native04_n04.lean --report gen/n04.report.json --state-out gen/n04.state.json 2>&1 | tail -15
rm -rf __pycache__
