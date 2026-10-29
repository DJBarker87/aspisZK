import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_069
set_option autoImplicit false
noncomputable section
namespace PV_L1E_Source_070
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
  Logged ((core.result.Result ((alloc.vec.Vec Std.U8) ×
    prover.MaskedFixtureAudit) verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  := do
  let r ← PV_L1D_Logged.lift (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      public1)
  let r1 ← PV_L1D_Logged.lift (core.result.Result.map_err
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      r ())
  let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let s1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ s ])))
    let a ← PV_L1D_Logged.lift (hash s1)
    let a1 ← PV_L1D_Logged.lift (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.impl.mask_nonce
        attempt)
    let context ← PV_L1D_Logged.lift (aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1
        a a1)
    let s2 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice
        (Array.make 30#usize [
          85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
          49#u8, 58#u8, 80#u8, 51#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8,
          84#u8, 69#u8, 45#u8, 65#u8, 84#u8, 84#u8, 69#u8, 77#u8, 80#u8, 84#u8
          ])))
    let s3 := alloc.vec.Vec.deref val
    let i ← PV_L1D_Logged.lift (transport.Variant.tag variant)
    let s4 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ i ])))
    let a2 ← PV_L1D_Logged.lift (aspis_core.state_only_hiding.StateOnlyHidingContext.encode context)
    let s5 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice a2))
    let s6 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 4#usize [ s2, s3, s4, s5 ])))
    let binding ← PV_L1D_Logged.lift (hash s6)
    PV_L1D_Source_069.produce
      aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
      public1 compiled variant hash context binding attempt nonce_store
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual)
    Pure.pure (r2, nonce_store)

theorem complete_result
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
  erase (produce public1 compiled variant hash attempt nonce_store) = prover.prove_masked_attempt public1 compiled variant hash attempt nonce_store := by
  unfold produce
  conv_rhs => unfold prover.prove_masked_attempt
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_069.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_069.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_069.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1E_Source_070
