cd "$(dirname "$0")"
python3 -B PCWF_gen_equalities.py --module AspisR1Qm31ArithmeticProbe.Funs \
 --fresh-dir ../prov-p1e-20261109/PCQF_E007_emitted/raw/PCQF_aspis_core_field_a --fresh-ns PCQF_aspis_core_field_a \
 --gate-source inputs/gate_AspisR1Qm31ArithmeticProbe_Funs.lean --gate-types-source inputs/gate_AspisR1Qm31ArithmeticProbe_Types.lean \
 --only inputs/only_qm31.json \
 --prune-fresh --out PRVEq_AspisR1Qm31ArithmeticProbe_Funs_f1.lean --report gen/qm31_f1.report.json --state-out gen/qm31_f1.state.json 2>&1 | tail -15
rm -rf __pycache__
