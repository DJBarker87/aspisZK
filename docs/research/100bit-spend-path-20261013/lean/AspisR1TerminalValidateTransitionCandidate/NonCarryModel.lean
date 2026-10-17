import AspisR1TerminalValidateTransitionCandidate.NonCarry
import R1AppendSemantics

set_option autoImplicit false
namespace AspisR1TerminalValidateTransitionCandidate.NonCarryModel
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

/-- Re-express the expanded actual-loop result at the maintained append-model
interface. The frozen-empty row definitions are definitionally identical. -/
theorem validate_loop_success_noncarry_shape_model
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (carry : UScalar UScalarTy.Usize)
    (hcarryRun : AspisBoundedControl.bounded_carry
      public1.transition.live_snapshot.next_pair_index = .ok carry)
    (hsuccess : AspisR1TerminalValidateTransitionCandidate.validate_transition_loop public1
      { start := 0#usize, «end» := 20#usize } carry = .ok (.Ok ())) :
    AspisR1.AppendSemantics.NonCarryShape
      (AspisR1.SemanticPublicModel.exactPublic public1) := by
  intro level hlevelNe
  have h := AspisR1TerminalValidateTransitionCandidate.NonCarry.validate_loop_success_noncarry_shape
    public1 carry hcarryRun hsuccess level hlevelNe
  have hempty : AspisR1TerminalValidateTransitionCandidate.RowMeaning.frozenEmptyModel
      level.castSucc = AspisR1.AppendNode.frozenEmpty level.castSucc := rfl
  change (AspisR1.SemanticPublicModel.exactPublic public1).nextFrontier level =
    if level.val < R0P.digestCarry
          (AspisR1.SemanticPublicModel.exactPublic public1).nextPairIndex ∨
        R0P.digestBitZero (AspisR1.SemanticPublicModel.exactPublic public1) level
    then AspisR1.AppendNode.frozenEmpty level.castSucc
    else (AspisR1.SemanticPublicModel.exactPublic public1).snapshotFrontier level
  rw [← hempty]
  exact h

#print axioms validate_loop_success_noncarry_shape_model
end AspisR1TerminalValidateTransitionCandidate.NonCarryModel
