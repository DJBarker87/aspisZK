"""Expose the two proved arithmetic kernels in the exact pinned finish body."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin47-20261028'
p=json.loads((E/'build-plan.json').read_text())['modules']['R1Z.ProverRwFullFuns'];b=(R/p['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==p['sha256']
s=b.decode();a=s.index('def prover.finish_opening\n');z=s.index('\n/--',a);src=s[a:z]
x=src.replace('def prover.finish_opening\n','def run\n',1)
x=x.replace('  (folded_salts : host_commitment.PrivateSalts) :','''  (folded_salts : host_commitment.PrivateSalts)
  (round_result : Result (Array aspis_core.field.wide_exact.WideExact 7#usize))
  (fold : aspis_core.field.wide_exact.WideExact → Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact)) :''')
x=x.replace('let c1 ← prover.round s1 s2','let c1 ← round_result').replace('let final_message ← prover.fold s7 alpha1 false','let final_message ← fold alpha1')
out='''import R1Z.PV_RunJoin_PrepareOperations47
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FinishContext47
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

'''+x+'''

theorem source (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (prepared : prover.PreparedOpening) (salts : host_commitment.PrivateSalts) :
    prover.finish_opening variant hash prepared salts=
      run variant hash prepared salts
        (prover.round (alloc.vec.Vec.deref prepared.q1) (alloc.vec.Vec.deref prepared.w1))
        (fun a => prover.fold (alloc.vec.Vec.deref prepared.q1) a false) := by rfl
#print axioms source
end R1Z.PV_RunJoin_FinishContext47
'''
(R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_FinishContext47.lean').write_text(out)
(E/'finish-context-source-identity.json').write_text(json.dumps(dict(pin=p,original_body_sha256=hashlib.sha256(src.encode()).hexdigest(),change='abstract exact c1 round Result and final primal-fold function; preserve tree, transcript, queries, public check and every Result branch'),indent=2)+'\n')
