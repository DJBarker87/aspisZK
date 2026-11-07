import NMT_345AfterSum
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- The exact checked-add Option is consumed, with no unchecked extent or
success premise. The None arm returns the actual InvalidAccountData value. -/
theorem sum_call {W : Type} (c : Calls) (s : HasSum W) :
 afterSum c s =
 tryStep (NMT_stage1_owned.core.option.Option.ok_or s.checkedSum NMT_stage1_owned.solana_program_error.ProgramError.InvalidAccountData)
  (fun end_ => raw11 c ⟨s.toHasStart.toHasLength.toProofData,s.proofStart,end_⟩) := by
 unfold afterSum tryStep NMT_stage1_owned.core.option.Option.ok_or
 cases h : s.checkedSum <;> rfl
#print axioms sum_call
end NMT_345
