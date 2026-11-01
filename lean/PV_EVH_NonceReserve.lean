import PV_EVH_NonceWorld
import PV_EVH_NonceReserveFallible
import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NonceReserve
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  op23_OPEN : ∀ (arg0 : std.io.error.Error), P (core.io.error.ErrorKind)

structure Compatible (c : Callees) : Prop where
  op23_fixed : ∀ (arg0 : std.io.error.Error), FinishedView (c.op23_OPEN arg0) (std.io.error.Error.kind arg0)

def run
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) (fileAnswers : PV_EVH_NonceWorld.Answers) (fallibleCallees : PV_EVH_NonceReserveFallible.Callees) (pathCallees : PV_EVH_NoncePath.Callees) (c : Callees) : P (Bool ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let (r, self1) ← PV_EVH_NonceReserveFallible.run self statement_digest mask_nonce fileAnswers pathCallees fallibleCallees
  match r with
  | core.result.Result.Ok reserved =>
    pure (reserved, self1)
  | core.result.Result.Err error =>
    let ek ← c.op23_OPEN error
    pure (false, { self1 with last_error := (some ek) })

theorem run_fixed
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) (fileAnswers : PV_EVH_NonceWorld.Answers) (fallibleCallees : PV_EVH_NonceReserveFallible.Callees) (pathCallees : PV_EVH_NoncePath.Callees) (c : Callees) (compatible : Compatible c) (files_same : PV_EVH_NonceWorld.Compatible fileAnswers) (fallible_same : PV_EVH_NonceReserveFallible.Compatible fallibleCallees) (path_same : PV_EVH_NoncePath.Compatible pathCallees) :
    FinishedView (run self statement_digest mask_nonce fileAnswers fallibleCallees pathCallees c) (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve self statement_digest mask_nonce) := by
  unfold run aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact PV_EVH_NonceReserveFallible.run_fixed _ _ _ fileAnswers pathCallees fallibleCallees fallible_same files_same path_same
  · rintro ⟨r, self1⟩
    try dsimp only
    cases r with
    | Ok reserved =>
      exact PV_EVH_Prefix.lift_fixed _
    | Err error =>
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact compatible.op23_fixed _
      · intro ek
        exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_NonceReserve
