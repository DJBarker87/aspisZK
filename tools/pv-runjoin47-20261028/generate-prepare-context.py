"""Expose only the constructor Result argument in the exact pinned prepare body."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin47-20261028'
p=json.loads((E/'build-plan.json').read_text())['modules']['R1Z.ProverRwFullFuns']
b=(R/p['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==p['sha256']
s=b.decode();a=s.index('def prover.prepare_opening\n');z=s.index('\n/--',a);src=s[a:z]
x=src.replace('def prover.prepare_opening\n','def run\n',1).replace('  Result (core.result.Result prover.PreparedOpening verifier.Error)','  Result (core.result.Result prover.PreparedOpening verifier.Error)',1)
x=x.replace('  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :','  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)\n  (constructor : Result (core.result.Result weights.Weights verifier.Error)) :',1)
needle='let r ← weights.Weights.new variant sem.alpha sem.z';assert x.count(needle)==1;x=x.replace(needle,'let r ← constructor')
out='''import R1Z.PV_RunJoin_WeightConstructorInstalled47
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareContext47
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

'''+x+'''

theorem source (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (backend : prover.Backend)
    (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :
    prover.prepare_opening variant hash backend sem=
      run variant hash backend sem (weights.Weights.new variant sem.alpha sem.z) := by rfl
#print axioms source
end R1Z.PV_RunJoin_PrepareContext47
'''
(R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PrepareContext47.lean').write_text(out)
(E/'prepare-context-source-identity.json').write_text(json.dumps(dict(module='R1Z.ProverRwFullFuns',pin=p,original_body_sha256=hashlib.sha256(src.encode()).hexdigest(),change='abstract exactly one constructor Result argument; every other source call, branch, tag, field and order retained'),indent=2)+'\n')
