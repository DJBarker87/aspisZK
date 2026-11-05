import NHJ_StdCopy
import S2W_D189Entry
set_option autoImplicit false
noncomputable section
namespace NHJ_SnapshotEntry
open Aeneas Aeneas.Std Result
open AspisR1.S2W_D189Entry

theorem len_iff (bytes : Slice U8) (n : Usize) :
    Slice.len bytes = n ↔ bytes.val.length = n.val := by
  constructor
  · intro h
    exact congrArg UScalar.val h
  · intro h
    exact UScalar.eq_of_val_eq h

/-- Computed producer value agrees with the actual deployed entry model.
No returned snapshot, successful parent or output equality is assumed.
This is the model join, not a new native SDK/allocator interpretation. -/
theorem source (e : Entry) (a : Nat) (l1 l2 : Usize) :
    let old := (e.records (e.handles a).1).owned
    NGL_SnapshotModel.run NHJ_StdCopy.copy old.key old.owner
      old.is_signer old.is_writable old.executable l1 l2
      (.Ok (e.buffers (e.handles a).1)) = ok (e.snapshot a l1.val l2.val) := by
  dsimp only
  have test :
      (Slice.len (e.buffers (e.handles a).1) = l1 ∨ Slice.len (e.buffers (e.handles a).1) = l2) ↔
      ((e.buffers (e.handles a).1).val.length = l1.val ∨ (e.buffers (e.handles a).1).val.length = l2.val) :=
    or_congr (len_iff _ l1) (len_iff _ l2)
  by_cases admitted : Slice.len (e.buffers (e.handles a).1) = l1 ∨ Slice.len (e.buffers (e.handles a).1) = l2
  · rw [NGL_SnapshotModel.accepted_length _ _ _ _ _ _ _ _ _ admitted]
    have natural := test.mp admitted
    simp only [NHJ_StdCopy.copy,NHJ_StdCopy.to_vec_exact,bind_tc_ok]
    unfold Entry.snapshot
    dsimp only
    rw [if_pos natural]
    rfl
  · rw [NGL_SnapshotModel.rejected_length _ _ _ _ _ _ _ _ _
      (fun first => admitted (Or.inl first)) (fun second => admitted (Or.inr second))]
    have natural : ¬ ((e.buffers (e.handles a).1).val.length = l1.val ∨ (e.buffers (e.handles a).1).val.length = l2.val) :=
      fun h => admitted (test.mpr h)
    unfold Entry.snapshot
    dsimp only
    rw [if_neg natural]
#print axioms len_iff
#print axioms source
end NHJ_SnapshotEntry
