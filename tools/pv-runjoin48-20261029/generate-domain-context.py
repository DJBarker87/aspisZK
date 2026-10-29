"""Factor only the final domain Result handling from exact prepare operations."""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin48-20261029'
p=json.loads((E/'build-plan.json').read_text())['modules']['R1Z.ProverRwFullFuns'];b=(R/p['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==p['sha256']
s=(R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PrepareOperations47.lean').read_text();a=s.index('def run\n');z=s.index('\n\ntheorem source',a);body=s[a:z]
a=body.index('        let r2 ←\n');z=body.index('\n      | core.ops.control_flow.ControlFlow.Break residual =>',a)
old=body[a:z];exp=old[old.index('          host_commitment.EncodingDomain.evaluate'):old.index('\n        let r3 ←')]
body=body[:a]+'''        PV_RunJoin_PreparedDomain48.run backend sem transcript3 y1 gamma inactive kappa alpha0
          c0bytes q1 w1 (
'''+exp+''')'''+body[z:]
out='''import R1Z.PV_RunJoin_PreparedDomain48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareDomainContext48
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
      run variant hash backend sem coefficients constructor materialize := by rfl
#print axioms source
end R1Z.PV_RunJoin_PrepareDomainContext48
'''
path=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PrepareDomainContext48.lean'
if '--check' in sys.argv:assert path.read_text()==out
else:path.write_text(out)
(E/'prepare-domain-context-source-identity.json').write_text(json.dumps(dict(frozen_source=p,operations_source_sha256=hashlib.sha256(s.encode()).hexdigest(),removed_suffix_sha256=hashlib.sha256(old.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),change='factor only domain map_err/branch/from_residual and exact PreparedOpening fields; all prefix calls and both earlier Rust error branches retained'),indent=2)+'\n')
