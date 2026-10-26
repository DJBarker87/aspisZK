"""Exact post-reservation source continuation, with no callee substitution."""
from pathlib import Path
import hashlib,re,json,sys
r=Path(__file__).resolve().parents[3];p=r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean';s=p.read_text();a=s.index('def prover.prove_masked_with_attempt\n');b=s.index('\n/--',a);old=s[a:b].strip();start=old.index('  let (r, nonce_store1) ←');end=old.index('  let r1 ←',start);call=old[start:end]
header=old[:start].replace('def prover.prove_masked_with_attempt','def afterReserve').replace('  (nonce_store : T0) :','''  (r : core.result.Result
    (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
      aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError)
  (nonce_store1 : T0) :''')
t='''import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwBodyStoreSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
'''+header+old[end:]+'\nend R1Z.ProverRwBodyStoreSource\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwBodyStoreSource.lean'
if '--check' in sys.argv:assert o.read_text()==t
else:
 o.write_text(t)
 (r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-resume/body-store-source.json').write_text(json.dumps(dict(path=str(p.relative_to(r)),source_declaration_sha256=hashlib.sha256(old.encode()).hexdigest(),first_call=call,output_sha256=hashlib.sha256(t.encode()).hexdigest(),change='First reservation-result bind becomes two continuation arguments; every remaining emitted byte is retained. No operation/dictionary/body result substitution.'),indent=2)+'\n')
print(hashlib.sha256(t.encode()).hexdigest())
