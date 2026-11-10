cd "$(dirname "$0")"
R=""
for n in new_loop1_loop0 new_loop0_loop0 new_loop1 new_loop0 new; do R="$R --rename-fresh weights.Weights.$n.=weights_$n. --rename-fresh weights.Weights.$n=weights_$n"; done
PCWJ_S2FIRST=weights_new,state_only_prefix.state_only_statement_points,state_only_prefix.r0.statement_points,weights.Weights.new,aspis_core.state_only_prefix.state_only_statement_points,aspis_core.state_only_prefix.r0.statement_points python3 -B PCWJ_gen_equalities.py --module FIn_WeightsFuns \
 --fresh-dir PCWJ_E008_emitted/raw/PCWJ_weightsoff --fresh-ns PCWJ_weightsoff \
 --gate-source inputs/gate_FIn_WeightsFuns.lean --gate-types-source inputs/gate_FIn_WeightsTypes.lean --gate-namespace FIn_WeightsExtract \
 $R --rename-fresh weights.Weights.=Weights. --rename-fresh weights.Weights=Weights --rename-fresh weights.double=double --rename-fresh transport.TAU=TAU \
 --rename-fresh transport.Variant=FInVariant --rename-fresh verifier.Error=FInError \
 --rename-fresh aspis_core.state_only_prefix.=state_only_prefix. --rename-fresh aspis_core.field.=field. --rename-fresh aspis_core.circle.=circle. \
 --prune-fresh --out PRVEq_FIn_WeightsFuns_b5.lean --report gen/weights_b5.report.json --state-out gen/weights_b5.state.json 2>&1 | tail -25
rm -rf __pycache__
