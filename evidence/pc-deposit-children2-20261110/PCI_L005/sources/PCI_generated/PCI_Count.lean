import PCF_CountSlice
import AdapterRwTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_Count
abbrev ProgramResult := core.result.Result Unit AdapterRw.solana_program_error.ProgramError
/-- Exact Rust ProgramResult constructors. No ABI quotient. -/
def reply : PCF_Count.Reply → ProgramResult
  | .ok => .Ok ()
  | .notEnoughKeys => .Err .NotEnoughAccountKeys
  | .invalidArgument => .Err .InvalidArgument
/-- Mechanical source fission changes only accounts.len() to its usize metadata. -/
def fission (len expected : Nat) : ProgramResult :=
  if len ≠ expected then
    if len < expected then .Err .NotEnoughAccountKeys else .Err .InvalidArgument
  else .Ok ()

theorem all_counts (len expected : Nat) :
    fission len expected = reply (PCF_Count.source len expected) := by
  by_cases he : len=expected <;> by_cases hl : len<expected <;>
    simp [fission,PCF_Count.source,reply,he,hl]

/-- All slice extents and all expected machine words, including both Err arms;
    the slice and all payload values are untouched. -/
theorem complete {T : Type} (accounts : Slice T) (expected : Usize) :
    fission accounts.length expected.val = reply (PCF_Count.source accounts.length expected.val) ∧
    PCF_CountSliceRef.count_reference accounts expected =
      ok (PCF_CountWord.tag (PCF_Count.source accounts.length expected.val)) :=
  ⟨all_counts _ _,PCF_CountSlice.complete accounts expected⟩

#print axioms all_counts
#print axioms complete
end PCI_Count
