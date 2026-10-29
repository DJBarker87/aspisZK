"""Expose only the successful-material continuation, preserving request order."""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin49-20261029'
s=(L/'PV_RunJoin_PrepareClaimContext48.lean').read_text()
body=s[s.index('def run\n'):s.index('\n\ntheorem source')]
old='''    Result aspis_core.field.wide_exact.WideExact) :'''
new='''    Result aspis_core.field.wide_exact.WideExact)
  (tail : host_transcript.Transcript aspis_core.digest.LegacyHashFn → alloc.vec.Vec U8 →
    aspis_core.field.wide_exact.WideExact → aspis_core.field.wide_exact.WideExact →
    aspis_core.field.wide_exact.WideExact → Slice aspis_core.field.wide_exact.WideExact →
    Slice aspis_core.field.wide_exact.WideExact → Result (core.result.Result prover.PreparedOpening verifier.Error)) :'''
assert body.count(old)==1;body=body.replace(old,new)
a=body.index('        let s6 := alloc.vec.Vec.deref q');b=body.index('\n      | core.ops.control_flow.ControlFlow.Break residual =>',a)+1
removed=body[a:b];body=body[:a]+'''        tail transcript2 y1 gamma inactive kappa (alloc.vec.Vec.deref q) (alloc.vec.Vec.deref val1)
'''+body[b:]
header='''import R1Z.PV_RunJoin_PrepareClaimContext48
import R1Z.PV_RunJoin_PrepareTail48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareMaterialContext49
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
'''
source=s[s.index('theorem source'):s.index('#print axioms source')]
# Keep the original theorem's parameter list and extend with claim/inactive parameters.
a=source.index(' :\n    PV_RunJoin_PrepareOperations47.run')
source=source[:a]+'''\n    (claim : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize) →
      aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact → Result (alloc.vec.Vec U8))
    (inactiveValue : Slice aspis_core.field.wide_exact.WideExact → weights.Weights → Result aspis_core.field.wide_exact.WideExact) :
    PV_RunJoin_PrepareClaimContext48.run variant hash backend sem coefficients constructor materialize claim inactiveValue=
      run variant hash backend sem coefficients constructor materialize claim inactiveValue
        (PV_RunJoin_PrepareTail48.run variant hash backend sem) := by rfl
'''
out=header+'\n'+body+'\n\n'+source+'#print axioms source\nend R1Z.PV_RunJoin_PrepareMaterialContext49\n'
p=L/'PV_RunJoin_PrepareMaterialContext49.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
(E/'material-context-source-identity.json').write_text(json.dumps(dict(input='PV_RunJoin_PrepareClaimContext48',input_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),removed_sha256=hashlib.sha256(removed.encode()).hexdigest(),tags_preserved=[27,28],request_order_preserved=True),indent=2)+'\n')
