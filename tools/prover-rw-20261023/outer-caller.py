#!/usr/bin/env python3
"""Install the proved public-prefix cut into the literal emitted caller."""
from pathlib import Path
import argparse,hashlib,json
root=Path(__file__).resolve().parents[2]
p=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwOuterPrefix.lean'
s=p.read_text();a=s.index('def caller\n');b=s.index('\ntheorem attempt_factor',a)
d=s[a:b].rstrip()
old='let (context,binding) ← prepare val variant hash attempt.mask_nonce'
assert d.count(old)==1
d=d.replace(old,'let (context,binding) ← ProverRwOuterFrames.run val variant hash attempt.mask_nonce')
t='''import R1Z.ProverRwOuterFrames
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterCaller
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

'''+d+'''

omit [ExternalFuns] in
theorem source_entry (ops : ExternalFuns)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
    letI : ExternalFuns := ProverRwOuterTag.selected ops
    prover.prove_masked_attempt pub compiled v hash attempt store =
      caller pub compiled v hash attempt store := by
  letI : ExternalFuns := ProverRwOuterTag.selected ops
  rw [ProverRwOuterPrefix.attempt_factor]
  unfold ProverRwOuterPrefix.caller caller
  simp only [ProverRwOuterPrepare.prepare_direct,ProverRwOuterFrames.direct_run]
  rfl

#print axioms source_entry
end R1Z.ProverRwOuterCaller
'''
out=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwOuterCaller.lean'
a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
if args.check:assert out.read_text()==t
else:out.write_text(t)
print(json.dumps({'source':str(p.relative_to(root)),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(t.encode()).hexdigest(),'substitution':'Only prepare replaced by proved OuterFrames.run; all serializer/error/body/store operations retained.'}))
