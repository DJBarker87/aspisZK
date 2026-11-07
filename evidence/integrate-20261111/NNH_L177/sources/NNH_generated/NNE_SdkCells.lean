import RSL_Base
import NLF_RefCell
set_option autoImplicit false
namespace NNE_SdkCells
/-- Full token ledger and data payload; no byte or token coordinate is selected. -/
def cell (c : RSL.Cell) : NLF_RefCell.Cell RSL.Bytes :=
 ⟨c.payload,c.readers,c.writer⟩
def kind : RSL.Kind → NLF_RefCell.Kind
 | .shared => .shared
 | .exclusive => .exclusive

theorem shared_admission (c : RSL.Cell) (t : Nat) (fresh : t ∉ c.readers) :
 NLF_RefCell.shared (cell c) t =
 if RSL.sharedOk c then .ok (cell {c with readers := t :: c.readers})
 else .error .conflict := by
 simp [NLF_RefCell.shared,cell,RSL.sharedOk,fresh,Option.isNone_iff_eq_none]

theorem exclusive_admission (c : RSL.Cell) (t : Nat) :
 NLF_RefCell.exclusive (cell c) t =
 if RSL.exclusiveOk c then .ok (cell {c with writer := some t})
 else .error .conflict := by
 simp [NLF_RefCell.exclusive,cell,RSL.exclusiveOk,Option.isNone_iff_eq_none,List.isEmpty_iff]

theorem shared_release (c : RSL.Cell) (t : Nat)
 (live : c.writer = none ∧ t ∈ c.readers) :
 NLF_RefCell.dropShared (cell c) t = .ok (cell {c with readers := c.readers.erase t}) := by
 simp [NLF_RefCell.dropShared,cell,live.1,live.2]

theorem exclusive_release (c : RSL.Cell) (t : Nat) (live : c.writer = some t) :
 NLF_RefCell.dropExclusive (cell c) t = .ok (cell {c with writer := none}) := by
 simp [NLF_RefCell.dropExclusive,cell,live]

theorem payload_identity (c : RSL.Cell) : (cell c).payload = c.payload := rfl

theorem token_identity (c : RSL.Cell) :
 (cell c).readers = c.readers ∧ (cell c).writer = c.writer := ⟨rfl,rfl⟩
#print axioms shared_admission
#print axioms exclusive_admission
#print axioms shared_release
#print axioms exclusive_release
#print axioms payload_identity
#print axioms token_identity
end NNE_SdkCells
