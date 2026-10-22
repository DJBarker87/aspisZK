import MultiproofConeSortOrder

set_option autoImplicit false
namespace AspisR1.MultiproofConeSortPermutation
open Aeneas Aeneas.Std Result MultiproofSortRef
open AspisR1.MultiproofConeSortStep

private theorem adjacent_perm {α : Type} [Inhabited α] (xs : List α) (i : Nat)
    (bound : i+1<xs.length) :
    ((xs.set i xs[i+1]!).set (i+1) xs[i]!).Perm xs := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at bound
    | cons a xs =>
      cases xs with
      | nil => simp at bound
      | cons b xs => simpa using List.Perm.swap a b xs
  | succ i ih =>
    cases xs with
    | nil => simp at bound
    | cons a xs => simpa using (ih xs (by simpa using bound)).cons a

/-- Each checked source swap preserves the complete array multiset, whether
or not the prefix is sorted. Stop is the identity permutation. -/
theorem insert_step_perm (keys : Array U64 16#usize) (cursor : Usize)
    (bound : cursor.val<16) :
    ∃ step, sort_reference.insert_step keys cursor=ok step ∧
      (match step with | .Done out => out.val | .Next out _ => out.val).Perm keys.val := by
  obtain ⟨step,eqstep,post⟩ := insert_step_total keys cursor bound
  refine ⟨step,eqstep,?_⟩
  cases step with
  | Done out =>
    obtain ⟨rfl,_⟩ := post
    exact List.Perm.refl _
  | Next out lower =>
    obtain ⟨position,_,rfl⟩ := post
    simp only [Array.set_val_eq]
    rw [←position]
    exact adjacent_perm keys.val lower.val (by have len : keys.val.length=16 := keys.property;omega)

#print axioms adjacent_perm
#print axioms insert_step_perm
end AspisR1.MultiproofConeSortPermutation
