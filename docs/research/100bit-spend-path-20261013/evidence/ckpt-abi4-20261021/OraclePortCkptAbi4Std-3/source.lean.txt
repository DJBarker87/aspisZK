import OraclePortCkptAbi3OwnedIter
import Aeneas.Std.SliceIter

/-! Inspect the live imported std operations before adopting their semantics.
Only the bounded-list content model is claimed. -/
#print Aeneas.Std.core.slice.iter.IteratorSliceIter.next
#print Aeneas.Std.core.slice.iter.IteratorIterMut.next
#print Aeneas.Std.alloc.vec.Vec.with_capacity
#print Aeneas.Std.alloc.vec.Vec.new
#print Aeneas.Std.core.slice.Slice.iter_mut
#print Aeneas.Std.Slice.setAtNat

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.OraclePortCkptAbi4Std

def sharedDrain {T : Type} : Nat → core.slice.iter.Iter T →
    Result (List T × core.slice.iter.Iter T)
  | 0, it => ok ([],it)
  | n+1, it => do
      let (item,rest) ← core.slice.iter.IteratorSliceIter.next it
      match item with
      | none => ok ([],rest)
      | some x => do
          let (xs,last) ← sharedDrain n rest
          ok (x::xs,last)

/-- Exact ordered content of every bounded shared iteration interval; the
backing slice is unchanged, including outside the visited interval. -/
theorem shared_interval {T : Type} (s : Slice T) (n i : Nat)
    (bound : i+n ≤ s.val.length) :
    sharedDrain n ⟨s,i⟩ = ok
      (List.ofFn (fun j : Fin n => s.val[i+j.val]'(by have := j.isLt; omega)),⟨s,i+n⟩) := by
  induction n generalizing i with
  | zero => simp only [sharedDrain,List.ofFn_zero,Nat.add_zero]
  | succ n ih =>
    have hi : i < s.val.length := by omega
    have hn : i+1+n ≤ s.val.length := by omega
    simp only [sharedDrain,core.slice.iter.IteratorSliceIter.next]
    rw [dif_pos (show i < s.len.val from hi)]
    change (do
      let (xs,last) ← sharedDrain n ⟨s,i+1⟩
      ok (s.val[i]::xs,last)) = _
    rw [ih (i+1) hn]
    simp only [bind_tc_ok,List.ofFn_succ,Fin.val_zero,Fin.val_succ,Nat.add_zero,
      Nat.add_assoc,Nat.add_comm 1]

theorem shared_exhausted {T : Type} (s : Slice T) :
    core.slice.iter.IteratorSliceIter.next ⟨s,s.val.length⟩ =
      ok (none,⟨s,s.val.length⟩) := by
  unfold core.slice.iter.IteratorSliceIter.next
  exact dif_neg (by change ¬ s.val.length < s.val.length; omega)

/-- The real mutable std next/back operation writes the supplied value back
at the original cursor and retains the advanced cursor and other elements. -/
theorem mutable_writeback {T : Type} (s : Slice T) (i : Nat) (x : T)
    (bound : i < s.val.length) :
    (do
      let (old,it,back) ← core.slice.iter.IteratorIterMut.next ⟨s,i⟩
      ok (old,it,back it (some x))) =
      ok (some s.val[i],(⟨s,i+1⟩ : core.slice.iter.IterMut T),
        (⟨s.setAtNat i x,i+1⟩ : core.slice.iter.IterMut T)) := by
  simp only [core.slice.iter.IteratorIterMut.next]
  rw [dif_pos (show i < s.len.val from bound)]
  rfl

/-- The imported content model erases the requested capacity completely.
A physical capacity witness cannot be recovered from its returned Vec. -/
theorem no_requested_capacity :
    ¬ ∃ capacity : alloc.vec.Vec Unit → Nat,
      ∀ n : Usize, capacity (alloc.vec.Vec.with_capacity Unit n) = n.val := by
  rintro ⟨capacity,h⟩
  have h0 := h 0#usize
  have h1 := h 1#usize
  change capacity (alloc.vec.Vec.new Unit) = 0 at h0
  change capacity (alloc.vec.Vec.new Unit) = 1 at h1
  omega

#print axioms shared_interval
#print axioms shared_exhausted
#print axioms mutable_writeback
#print axioms no_requested_capacity
end AspisR1.OraclePortCkptAbi4Std
