import NBA_Installed
set_option autoImplicit false
namespace AspisR1.NBR_VecAppend
open Aeneas Aeneas.Std Result

/-- The exact U8 clone callback preserves each element of the SAME list. -/
theorem clone_list (xs : List U8) :
    List.mapM core.clone.CloneU8.clone xs=ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,core.clone.CloneU8,liftFun1,core.clone.impls.CloneU8.clone,
      bind_tc_ok,ih]
    rfl

theorem clone_slice (xs : Slice U8) : Slice.clone core.clone.CloneU8.clone xs=ok xs := by
  unfold Slice.clone List.clone
  rw [clone_list,bind_tc_ok]

/-- Exact concatenation with the std capacity precondition derived by callers.
No clone success or output byte equation is a hypothesis. -/
theorem extend (before : alloc.vec.Vec U8) (input : Slice U8)
    (bound : before.length+input.length≤Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 before input=
      ok (⟨before.val++input.val,by simpa only [List.length_append] using bound⟩ : alloc.vec.Vec U8) := by
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_pos bound,clone_slice]

#print axioms clone_list
#print axioms clone_slice
#print axioms extend
end AspisR1.NBR_VecAppend
