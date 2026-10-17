import TerminalValidateTransitionEntryCarry
import AspisR1TerminalValidateTransitionCandidate.NonCarry

set_option autoImplicit false
namespace AspisR1TerminalValidateTransitionCandidate.EntryNonCarry
open Aeneas Aeneas.Std Result

abbrev Public := AspisR1TerminalValidateTransitionCandidate.EntryPublic
abbrev Usize := UScalar UScalarTy.Usize

/-- The complete checked outer entry reaches the exact `[0,20)` loop and
therefore establishes the loop-derived non-carry frontier relation for that
same public value. -/
theorem entry_success_noncarry_shape (public1 : Public) (capacity : Result Std.U64)
    (optionEqInst : core.cmp.PartialEq (Option Std.U64) (Option Std.U64))
    (hsuccess : AspisR1TerminalValidateTransitionCandidate.validate_transition_entry
      public1 capacity optionEqInst = .ok (.Ok ())) :
    ∀ level : Fin 20,
      level.val ≠ R0P.digestCarry
        (AspisR1.SemanticPublicModel.exactPublic public1).nextPairIndex →
      (AspisR1.SemanticPublicModel.exactPublic public1).nextFrontier level =
        if level.val < R0P.digestCarry
              (AspisR1.SemanticPublicModel.exactPublic public1).nextPairIndex ∨
            R0P.digestBitZero (AspisR1.SemanticPublicModel.exactPublic public1) level
        then AspisR1TerminalValidateTransitionCandidate.RowMeaning.frozenEmptyModel level.castSucc
        else (AspisR1.SemanticPublicModel.exactPublic public1).snapshotFrontier level := by
  obtain ⟨carry, hcarry, hloop⟩ :=
    AspisR1TerminalValidateTransitionCandidate.entry_success_reaches_bounded_carry_and_loop
      public1 capacity optionEqInst hsuccess
  exact AspisR1TerminalValidateTransitionCandidate.NonCarry.validate_loop_success_noncarry_shape
    public1 carry hcarry hloop

#print axioms entry_success_noncarry_shape
end AspisR1TerminalValidateTransitionCandidate.EntryNonCarry
