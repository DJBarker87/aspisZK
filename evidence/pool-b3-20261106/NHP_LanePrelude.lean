import NHP_AccountPrelude
set_option autoImplicit false
namespace NHP_LanePrelude
open NHP_AccountPrelude
/-- The lane reads its stored-bump window before checking signer/address. -/
def beforeStored (m : Metadata) (borrowSucceeds : Bool) : Option Error :=
  match program m with
  | some e => some e
  | none => if !borrowSucceeds then some .AccountBorrowFailed else none

theorem failed_borrow (m : Metadata) (h : program m = none) :
    beforeStored m false = some .AccountBorrowFailed := by simp [beforeStored,h]
#print axioms failed_borrow

theorem signer_does_not_change_prefix (m : Metadata) (s borrow : Bool) :
    beforeStored {m with signer := s} borrow = beforeStored m borrow := by rfl
#print axioms signer_does_not_change_prefix

theorem stored_window_domain (m : Metadata) (borrow : Bool) :
    beforeStored m borrow = none ↔
      m.ownerMatches = true ∧ m.executable = false ∧ m.writableMatches = true ∧
      borrow = true := by
  cases m with
  | mk o e w s => cases o <;> cases e <;> cases w <;> cases borrow <;>
      simp [beforeStored,program]
#print axioms stored_window_domain
end NHP_LanePrelude
