import OraclePortCkptAbi3StdInspection

/-! Content theorem for the actual imported owned Vec iterator. The model
has no capacity/allocator/Drop state, so this is not physical allocation. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.OraclePortCkptAbi3OwnedIter

theorem into_iter_exact {T : Type} (v : alloc.vec.Vec T) :
    alloc.vec.IntoIteratorVec.into_iter v = ok v := rfl

def drain {T : Type} : Nat → alloc.vec.into_iter.IntoIter T →
    Result (List T × alloc.vec.into_iter.IntoIter T)
  | 0, it => ok ([],it)
  | n+1, it => do
      let (item,rest) ← alloc.vec.into_iter.IteratorIntoIter.next it
      match item with
      | none => ok ([],rest)
      | some x => do
          let (xs,last) ← drain n rest
          ok (x::xs,last)

/-- The length-indexed iteration of the imported next model consumes every
owned element once, in order, and leaves the empty iterator. -/
theorem drain_exact {T : Type} (xs : List T) (bound : xs.length ≤ Usize.max) :
    drain xs.length ⟨xs,bound⟩ = ok (xs,⟨[],by simp⟩) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have tailBound : xs.length ≤ Usize.max := by
      simp only [List.length_cons] at bound
      omega
    simp only [List.length_cons,drain,alloc.vec.into_iter.IteratorIntoIter.next]
    change (do
      let (ys,last) ← drain xs.length ⟨xs,tailBound⟩
      ok (x::ys,last)) = _
    rw [ih tailBound]
    rfl

theorem owned_contents {T : Type} (v : alloc.vec.Vec T) :
    (do
      let it ← alloc.vec.IntoIteratorVec.into_iter v
      drain v.val.length it) = ok (v.val,⟨[],by simp⟩) := by
  rw [into_iter_exact]
  exact drain_exact v.val v.property

#print axioms into_iter_exact
#print axioms drain_exact
#print axioms owned_contents
#print Aeneas.Std.alloc.vec.into_iter.IteratorIntoIter.next
end AspisR1.OraclePortCkptAbi3OwnedIter
