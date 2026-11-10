# usage: bash pipe_n04.sh probe | bash pipe_n04.sh final LOG
cd "$(dirname "$0")"
M=RPu_FIq_Native04
GEN="python3 -B PCWP_gen_equalities.py --module $M --fresh-dir PCWP_E002_emitted/raw/PCWP_sop2 --fresh-ns PCWP_sop2 --gate-source inputs/$M.lean --gate-types-source inputs/$M.lean --rename-fresh aspis_core.= --rename-fresh aspis_statement.= --kind funs --only inputs/only_n04.json --fresh-prelude inputs/hmd_prelude.lean --tag _n04 --gate-extra-source inputs/RPu_FIq_Native01.lean --gate-extra-source inputs/RPu_FIq_Native02.lean --gate-extra-source inputs/RPu_FIq_Native03.lean --prune-fresh --out PRVEq_${M}_n04.lean"
if [ "$1" = probe ]; then $GEN --report gen/n04.report.json --state-out gen/n04.state.json | tail -1; fi
if [ "$1" = final ]; then $GEN --report gen/n04.report2.json --state gen/n04.state.json --lean-log "$2" --state-out gen/n04.state2.json | tail -1
python3 -B gen_loops.py PRVEq_${M}_n04.lean PRVEq_${M}_n04b.lean state_only_poseidon.internal_linear_lazy_loop0_loop0 state_only_poseidon.internal_linear_lazy_loop0 state_only_poseidon.internal_linear_lazy_loop1
python3 -B patch_n04.py PRVEq_${M}_n04b.lean PRVEq_${M}_n04c.lean; fi
rm -rf __pycache__ /tmp/_b_*
