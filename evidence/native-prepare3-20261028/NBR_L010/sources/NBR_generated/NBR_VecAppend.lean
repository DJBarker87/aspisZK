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
    simp only [List.mapM_cons,liftFun1,core.clone.impls.CloneU8.clone,
      bind_tc_ok,ih]
    rfl

theorem clone_slice (xs : Slice U8) : Slice.clone core.clone.CloneU8.clone xs=ok xs := by
  have h : List.mapM (liftFun1 core.clone.impls.CloneU8.clone) xs.val=ok xs.val := clone_list xs.val
  unfold Slice.clone List.clone
  split
  · rename_i v he
    have same : v=xs.val := Result.ok.inj (he.symm.trans h)
    subst v
    rfl
  · rename_i e he
    cases he.symm.trans h
  · rename_i he
    cases he.symm.trans h

/-- Exact concatenation with the std capacity precondition derived by callers.
No clone success or output byte equation is a hypothesis. -/
theorem extend (before : alloc.vec.Vec U8) (input : Slice U8)
    (bound : before.length+input.length≤Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 before input=
      ok (⟨before.val++input.val,by simpa only [List.length_append] using bound⟩ : alloc.vec.Vec U8) := by
  have h : Slice.clone (liftFun1 core.clone.impls.CloneU8.clone) input=ok input := clone_slice input
  unfold alloc.vec.Vec.extend_from_slice
  simp only [dif_pos bound]
  split
  · rename_i out he
    have same : out=input := Result.ok.inj (he.symm.trans h)
    subst out
    rfl
  · rename_i e he
    cases he.symm.trans h
  · rename_i he
    cases he.symm.trans h

theorem total (before : alloc.vec.Vec U8) (input : Slice U8)
    (bound : before.length+input.length≤Usize.max) :
    ∃ after, alloc.vec.Vec.extend_from_slice core.clone.CloneU8 before input=ok after ∧
      after.val=before.val++input.val := by
  exact ⟨_,extend before input bound,rfl⟩

#print axioms total
#print axioms clone_list
#print axioms clone_slice
#print axioms extend
end AspisR1.NBR_VecAppend
