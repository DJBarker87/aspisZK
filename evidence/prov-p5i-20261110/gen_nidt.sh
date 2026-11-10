cd "$(dirname "$0")"
F=../emission-repro-20261110/NMH_E003_emitted/raw/NHR_tx2_common
python3 -B PCWS_gen_equalities.py --module NID_ResumeEmissionTypes --fresh-dir $F --fresh-ns NHR_tx2_common \
 --gate-source inputs/gate_NID_ResumeEmissionTypes.lean --only inputs/only_nidt.json --prune-fresh \
 --out PRVEq_NID_ResumeEmissionTypes_s2.lean --report gen/nidt_s2.report.json --state-out gen/nidt_s2.state.json 2>&1 | tail -3 | cut -c1-300
rm -rf __pycache__
