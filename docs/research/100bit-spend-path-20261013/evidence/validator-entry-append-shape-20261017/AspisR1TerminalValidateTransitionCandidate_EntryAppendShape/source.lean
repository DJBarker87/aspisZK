import TerminalValidateTransitionEntryCarry
import AspisR1TerminalValidateTransitionCandidate.NonCarryModel
import R1AppendSemantics

set_option autoImplicit false
namespace AspisR1TerminalValidateTransitionCandidate.EntryAppendShape
open Aeneas Aeneas.Std Result

theorem successful_entry_append_shape
    (public1 : AspisR1TerminalValidateTransitionCandidate.EntryPublic)
    (capacity : Result Std.U64)
    (optionEqInst : core.cmp.PartialEq (Option Std.U64) (Option Std.U64))
    (hsuccess : AspisR1TerminalValidateTransitionCandidate.validate_transition_entry
      public1 capacity optionEqInst = .ok (.Ok ())) :
    AspisR1.AppendSemantics.NonCarryShape
      (AspisR1.SemanticPublicModel.exactPublic public1) := by
  obtain ⟨carry, hcarry, hloop⟩ :=
    AspisR1TerminalValidateTransitionCandidate.entry_success_reaches_bounded_carry_and_loop
      public1 capacity optionEqInst hsuccess
  exact AspisR1TerminalValidateTransitionCandidate.NonCarryModel.validate_loop_success_noncarry_shape_model
    public1 carry hcarry hloop

#print axioms successful_entry_append_shape
end AspisR1TerminalValidateTransitionCandidate.EntryAppendShape
