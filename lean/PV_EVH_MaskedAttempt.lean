import PV_EVH_AccountEntry
set_option autoImplicit false
noncomputable section
namespace PV_EVH_MaskedAttempt
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
open PV_EVH_AccountEntry (Public Compiled Hash)
open PV_EVH_RetryBody (Store Secrets AttemptOutcome)
variable [ExternalTypes] [ExternalFuns]
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext

/-- Individual unexpanded source callees, not a whole-attempt answer/trace.
These remain proof work; no native effect coverage is asserted for them. -/
structure Callees where
  publicBytes_OPEN : Public → P (core.result.Result (alloc.vec.Vec U8) aspis_core.state_only_prefix.r0.Error)
  hash_OPEN : Slice (Slice U8) → P (Array U8 32#usize)
  context_OPEN : Array U8 32#usize → Array U8 32#usize → P Context
  encode_OPEN : Context → P (Array U8 81#usize)
  tag_OPEN : transport.Variant → P U8
  withAttempt_OPEN : Context → Array U8 32#usize → Secrets → Store → P AttemptOutcome

structure Compatible (c : Callees) (public1 : Public) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) : Prop where
  publicBytes_fixed : ∀ p, FinishedView (c.publicBytes_OPEN p)
    (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p)
  hash_fixed : ∀ s, FinishedView (c.hash_OPEN s) (hash s)
  context_fixed : ∀ a b, FinishedView (c.context_OPEN a b)
    (aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1 a b)
  encode_fixed : ∀ a, FinishedView (c.encode_OPEN a)
    (aspis_core.state_only_hiding.StateOnlyHidingContext.encode a)
  tag_fixed : ∀ v, FinishedView (c.tag_OPEN v) (transport.Variant.tag v)
  withAttempt_fixed : ∀ context binding attempt store,
    FinishedView (c.withAttempt_OPEN context binding attempt store)
      (prover.prove_masked_with_attempt
        aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
        public1 compiled variant hash context binding attempt store)

/-- Source spine only; all effectful opaque callees above remain OPEN. -/
def run
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (c : Callees) : P AttemptOutcome := do
  let r ← c.publicBytes_OPEN public1
  let r1 ← PV_EVH_Prefix.lift (core.result.Result.map_err
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      r ())
  let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let s1 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ s ])))
    let a ← c.hash_OPEN s1
    let a1 ← PV_EVH_Prefix.lift (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.impl.mask_nonce
        attempt)
    let context ← c.context_OPEN a a1
    let s2 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice
        (Array.make 30#usize [
        85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
        49#u8, 58#u8, 80#u8, 51#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8,
        84#u8, 69#u8, 45#u8, 65#u8, 84#u8, 84#u8, 69#u8, 77#u8, 80#u8, 84#u8
        ])))
    let s3 := alloc.vec.Vec.deref val
    let i ← c.tag_OPEN variant
    let s4 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ i ])))
    let a2 ← c.encode_OPEN context
    let s5 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice a2))
    let s6 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice (Array.make 4#usize [ s2, s3, s4, s5 ])))
    let binding ← c.hash_OPEN s6
    c.withAttempt_OPEN context binding attempt nonce_store
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual)
    pure (r2, nonce_store)

theorem run_fixed
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (c : Callees)
    (compatible : Compatible c public1 compiled variant hash) :
    FinishedView (run public1 compiled variant hash attempt nonce_store c)
      (prover.prove_masked_attempt public1 compiled variant hash attempt nonce_store) := by
  unfold run prover.prove_masked_attempt
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact compatible.publicBytes_fixed _
  · intro r
    try dsimp only
    apply PV_EVH_Prefix.bind_fixed
    ·
      exact PV_EVH_Prefix.lift_fixed _
    · intro r1
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact PV_EVH_Prefix.lift_fixed _
      · intro cf
        try dsimp only
        cases cf with
        | Continue val =>
          let s := alloc.vec.Vec.deref val
          try dsimp only
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact PV_EVH_Prefix.lift_fixed _
          · intro s1
            try dsimp only
            apply PV_EVH_Prefix.bind_fixed
            ·
              exact compatible.hash_fixed _
            · intro a
              try dsimp only
              apply PV_EVH_Prefix.bind_fixed
              ·
                exact PV_EVH_Prefix.lift_fixed _
              · intro a1
                try dsimp only
                apply PV_EVH_Prefix.bind_fixed
                ·
                  exact compatible.context_fixed _ _
                · intro context
                  try dsimp only
                  apply PV_EVH_Prefix.bind_fixed
                  ·
                    exact PV_EVH_Prefix.lift_fixed _
                  · intro s2
                    let s3 := alloc.vec.Vec.deref val
                    try dsimp only
                    try dsimp only
                    apply PV_EVH_Prefix.bind_fixed
                    ·
                      exact compatible.tag_fixed _
                    · intro i
                      try dsimp only
                      apply PV_EVH_Prefix.bind_fixed
                      ·
                        exact PV_EVH_Prefix.lift_fixed _
                      · intro s4
                        try dsimp only
                        apply PV_EVH_Prefix.bind_fixed
                        ·
                          exact compatible.encode_fixed _
                        · intro a2
                          try dsimp only
                          apply PV_EVH_Prefix.bind_fixed
                          ·
                            exact PV_EVH_Prefix.lift_fixed _
                          · intro s5
                            try dsimp only
                            apply PV_EVH_Prefix.bind_fixed
                            ·
                              exact PV_EVH_Prefix.lift_fixed _
                            · intro s6
                              try dsimp only
                              apply PV_EVH_Prefix.bind_fixed
                              ·
                                exact compatible.hash_fixed _
                              · intro binding
                                exact compatible.withAttempt_fixed _ _ _ _
        | Break residual =>
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact PV_EVH_Prefix.lift_fixed _
          · intro r2
            exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_MaskedAttempt
