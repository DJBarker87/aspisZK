cd "$(dirname "$0")"
python3 -B PCWJ_gen_equalities.py --module AspisR1Post25Sampler.Funs \
 --fresh-dir PCWJ_E005_emitted/raw/PCWJ_post25e --fresh-ns PCWJ_post25e \
 --gate-source inputs/gate_AspisR1Post25Sampler_Funs.lean --gate-types-source inputs/gate_AspisR1Post25Sampler_Types.lean \
 \
 --rename-fresh aspis_core.field.wide_exact.canonical_qm31.=field.canonical_qm31. --rename-fresh aspis_core.field.wide_exact.canonical_qm31=field.canonical_qm31 --rename-fresh aspis_core.field.wide_exact.WideExact.=field.WideExact. --rename-fresh aspis_core.field.wide_exact.WideExact=field.WideExact --rename-fresh aspis_core.field.=field. \
 --only inputs/only_post25.json \
 --prune-fresh --out PRVEq_AspisR1Post25Sampler_Funs_a6.lean --report gen/post25_a6.report.json --state-out gen/post25_a6.state.json 2>&1 | tail -25
rm -rf __pycache__
# PCWJ manual shape for decode8 (generated rfl/delta shape times out at 200000 heartbeats): replace its theorem by a rewrite with the callee equalities.
python3 -B - <<'PY'
s=open('PRVEq_AspisR1Post25Sampler_Funs_a6.lean').read()
key='set_option maxHeartbeats 200000 in\ntheorem PRVEq.AspisR1Post25Sampler.Funs.sampler.decode8'
i=s.index(key); j=s.index('\n',s.index('#print axioms PRVEq.AspisR1Post25Sampler.Funs.sampler.decode8'))+1
man='''-- PCWJ manual shape for decode8: rewrite the two callees with the equalities proved above.
set_option maxHeartbeats 200000 in
theorem PRVEq.AspisR1Post25Sampler.Funs.sampler.decode8 : @AspisR1Post25Sampler.PRVFresh_AspisR1Post25Sampler_Funs.sampler.decode8 = @AspisR1Post25Sampler.sampler.decode8 := by
  have hc := PRVEq.AspisR1Post25Sampler.Funs.field.CM31.new
  have hw := PRVEq.AspisR1Post25Sampler.Funs.field.WideExact.new
  funext digits
  unfold AspisR1Post25Sampler.PRVFresh_AspisR1Post25Sampler_Funs.sampler.decode8 AspisR1Post25Sampler.sampler.decode8
  rw [hc, hw]
#print axioms PRVEq.AspisR1Post25Sampler.Funs.sampler.decode8
'''
open('PRVEq_AspisR1Post25Sampler_Funs_a6.lean','w').write(s[:i]+man+s[j:])
PY
rm -rf __pycache__
