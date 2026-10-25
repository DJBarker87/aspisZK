#!/usr/bin/env python3
"""Pin and factor the actual public-prefix caller; never alter native source."""
from pathlib import Path
import argparse,hashlib,json
root=Path(__file__).resolve().parents[2]
src=root/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=src.read_text(); start=s.index('def prover.prove_masked_attempt\n');end=s.index('\n/--',start);original=s[start:end]
start_pre=original.index('    let s := alloc.vec.Vec.deref val\n');end_pre=original.index('    prover.prove_masked_with_attempt\n',start_pre)
pre=original[start_pre:end_pre]
getter='''    let a1 ←
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.impl.mask_nonce
        attempt
'''
assert pre.count(getter)==1
pre=pre.replace(getter,'    let a1 := nonce\n')
pre='\n'.join(line[4:] for line in pre.splitlines())
prepare='''def prepare (val : alloc.vec.Vec U8) (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (nonce : Array U8 32#usize) :
    Result (aspis_core.state_only_hiding.StateOnlyHidingContext × Array U8 32#usize) := do
'''+''.join('  '+line+'\n' for line in pre.splitlines())+'  ok (context,binding)\n'
caller=original.replace('def prover.prove_masked_attempt','def caller',1)
caller=caller[:caller.index('    let s := alloc.vec.Vec.deref val\n')]+'''    let (context,binding) ← prepare val variant hash attempt.mask_nonce
'''+original[end_pre:]
text='''import R1Z.ProverRwEntropyIteration
/-! Source public-prefix factoring only. The constructor/encoder and native
hash/view interpretations are still explicit external operations. -/
set_option autoImplicit false
namespace R1Z.ProverRwOuterPrefix
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

'''+prepare+'\n'+caller+'''

theorem attempt_factor
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (variant : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
    prover.prove_masked_attempt pub compiled variant hash attempt store =
      caller pub compiled variant hash attempt store := by
  unfold caller prepare prover.prove_masked_attempt
  simp only [aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.impl.mask_nonce,
    bind_tc_ok,bind_assoc_eq,Aeneas.Std.uncurry]
  rfl

#print axioms attempt_factor
end R1Z.ProverRwOuterPrefix
'''
out=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwOuterPrefix.lean'
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
if args.check: assert out.read_text()==text
else: out.write_text(text)
print(json.dumps({'original_declaration':'prover.prove_masked_attempt','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'declaration_sha256':hashlib.sha256(original.encode()).hexdigest(),'output_sha256':hashlib.sha256(text.encode()).hexdigest(),'claim':'source prefix factoring; no native effect or PrefixContract instance'}))
