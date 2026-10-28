import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_Snapshots
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers
/-- Snapshot metadata is the same original record, including on deferred error. -/
theorem metadata (e : Entry) (a l₁ l₂ : Nat) :
    (e.snapshot a l₁ l₂).key = (e.records (e.handles a).1).owned.key ∧
    (e.snapshot a l₁ l₂).owner = (e.records (e.handles a).1).owned.owner ∧
    (e.snapshot a l₁ l₂).is_signer = (e.records (e.handles a).1).owned.is_signer ∧
    (e.snapshot a l₁ l₂).is_writable = (e.records (e.handles a).1).owned.is_writable ∧
    (e.snapshot a l₁ l₂).executable = (e.records (e.handles a).1).owned.executable := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩
 theorem original_length (e : Entry) (a l₁ l₂ : Nat) :
    (e.snapshot a l₁ l₂).length = .Ok (Slice.len (e.buffers (e.handles a).1)) := rfl
 theorem admitted_bytes (e : Entry) (a l₁ l₂ : Nat)
    (size : (e.buffers (e.handles a).1).val.length = l₁ ∨
      (e.buffers (e.handles a).1).val.length = l₂) :
    (e.snapshot a l₁ l₂).bytes = .Ok (e.buffers (e.handles a).1) := by
  simp only [Entry.snapshot, if_pos size]
 theorem deferred_error (e : Entry) (a l₁ l₂ : Nat)
    (size : ¬ ((e.buffers (e.handles a).1).val.length = l₁ ∨
      (e.buffers (e.handles a).1).val.length = l₂)) :
    (e.snapshot a l₁ l₂).bytes =
      .Err _root_.AdapterRw.solana_program_error.ProgramError.InvalidAccountData := by
  simp only [Entry.snapshot, if_neg size]
 theorem exactly_seven (e : Entry) : (e.second secondSizes).val.length = 7 := by
  simp only [Entry.second, List.length_ofFn]
#print axioms metadata
#print axioms original_length
#print axioms admitted_bytes
#print axioms deferred_error
#print axioms exactly_seven
end AspisR1.NCK_Snapshots
end
