"""Expose only claim/inactive callbacks in the checked prepare operations body."""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin48-20261029'
p=json.loads((E/'build-plan.json').read_text())['modules']['R1Z.ProverRwFullFuns']
f=(R/p['path']).read_bytes();assert hashlib.sha256(f).hexdigest()==p['sha256']
s=(R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PrepareOperations47.lean').read_text()
a=s.index('def run\n');b=s.index('\n\ntheorem source',a);body=s[a:b]
needle='  Result (core.result.Result prover.PreparedOpening verifier.Error)'
body=body.replace('verifier.Error)) :\n'+needle,'''verifier.Error))
  (claim : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize) →
    aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact → Result (alloc.vec.Vec U8))
  (inactiveValue : Slice aspis_core.field.wide_exact.WideExact → weights.Weights →
    Result aspis_core.field.wide_exact.WideExact) :
'''+needle,1)
assert '  (claim :' in body
assert body.count('prover.opening_claim_bytes s1')==1 and body.count('prover.opening_inactive s4 val')==1
body=body.replace('prover.opening_claim_bytes s1','claim s1').replace('prover.opening_inactive s4 val','inactiveValue s4 val')
out='''import R1Z.PV_RunJoin_PrepareOperations47
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareClaimContext48
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

'''+body+'''

theorem source (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (backend : prover.Backend)
    (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (coefficients : Result (alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize)))
    (constructor : Result (core.result.Result weights.Weights verifier.Error))
    (materialize : weights.Weights → aspis_core.field.wide_exact.WideExact →
      Result (core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) verifier.Error)) :
    PV_RunJoin_PrepareOperations47.run variant hash backend sem coefficients constructor materialize=
      run variant hash backend sem coefficients constructor materialize
        prover.opening_claim_bytes prover.opening_inactive := by rfl
#print axioms source
end R1Z.PV_RunJoin_PrepareClaimContext48
'''
path=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PrepareClaimContext48.lean'
if '--check' in sys.argv:assert path.read_text()==out
else:path.write_text(out)
(E/'prepare-claim-context-source-identity.json').write_text(json.dumps(dict(frozen_source=p,operations_source_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),changes=['abstract exactly opening_claim_bytes callback','abstract exactly opening_inactive callback'],all_other_calls_branches_tags_fields_retained=True),indent=2)+'\n')
