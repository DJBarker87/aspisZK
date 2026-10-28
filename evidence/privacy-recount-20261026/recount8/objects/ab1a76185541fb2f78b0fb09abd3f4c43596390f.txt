import R1Z.ProverRwQueryAttempt
/-! Exact emitted caller with its proved query component installed. Generated
by tools/prover-rw-20261023/query-composition.py; no native source change. -/
set_option autoImplicit false
namespace R1Z.ProverRwQueryNativeAttempt
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def nativeAttempt
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
  Result ((core.result.Result ((alloc.vec.Vec Std.U8) ×
    prover.MaskedFixtureAudit) verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  := do
  let r ←
    aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      public1
  let r1 ←
    core.result.Result.map_err
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let s1 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ s ]))
    let a ← hash s1
    let a1 ←
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.impl.mask_nonce
        attempt
    let context ←
      aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1
        a a1
    let s2 ←
      Aeneas.Std.lift (Array.to_slice
        (Array.make 30#usize [
          85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
          49#u8, 58#u8, 80#u8, 51#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8,
          84#u8, 69#u8, 45#u8, 65#u8, 84#u8, 84#u8, 69#u8, 77#u8, 80#u8, 84#u8
          ]))
    let s3 := alloc.vec.Vec.deref val
    let i ← transport.Variant.tag variant
    let s4 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ i ]))
    let a2 ←
      aspis_core.state_only_hiding.StateOnlyHidingContext.encode context
    let s5 ← Aeneas.Std.lift (Array.to_slice a2)
    let s6 ← Aeneas.Std.lift (Array.to_slice (Array.make 4#usize [ s2, s3, s4, s5 ]))
    let binding ← hash s6
    ProverRwQueryAttempt.attempt
      aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
      public1 compiled variant hash context binding attempt nonce_store
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual
    ok (r2, nonce_store)

set_option backward.isDefEq.respectTransparency false in
theorem native_attempt_exact (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (variant : transport.Variant) (h : Slice (Slice U8) → Result (Array U8 32#usize))
    (secret : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
    prover.prove_masked_attempt pub compiled variant h secret s = nativeAttempt pub compiled variant h secret s := by
  simp only [prover.prove_masked_attempt,nativeAttempt,ProverRwQueryAttempt.attempt_exact]
  try rfl

#print axioms native_attempt_exact
end R1Z.ProverRwQueryNativeAttempt
