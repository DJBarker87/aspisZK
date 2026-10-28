import Aeneas.Std
namespace PV_B3P_VecValue226
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem push_value (v : alloc.vec.Vec U8) (x : U8) (hb : v.val.length < Usize.max) :
    ∃ out, alloc.vec.Vec.push v x = .ok out ∧ out.val = v.val ++ [x] :=
  WP.spec_imp_exists (alloc.vec.Vec.push_spec v x hb)

set_option backward.isDefEq.respectTransparency false in
theorem extend_value (inst : core.clone.Clone U8) (v : alloc.vec.Vec U8) (s : Slice U8)
    (hb : v.val.length + s.val.length ≤ Usize.max)
    (hc : Slice.clone inst.clone s = .ok s) :
    ∃ out, alloc.vec.Vec.extend_from_slice inst v s = .ok out ∧ out.val = v.val ++ s.val := by
  unfold alloc.vec.Vec.extend_from_slice
  split
  · split
    · rename_i s' he
      have hs : s' = s := Result.ok.inj (he.symm.trans hc)
      cases hs
      exact ⟨_,rfl,rfl⟩
    · rename_i e he
      rw [hc] at he
      cases he
    · rename_i he
      rw [hc] at he
      cases he
  · contradiction

theorem mapM_id (xs : List U8) : List.mapM (fun b : U8 => Result.ok b) xs = .ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons,ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem u8_clone (s : Slice U8) : Slice.clone core.clone.CloneU8.clone s = .ok s := by
  rcases s with ⟨xs,hxs⟩
  change Slice.clone (fun b : U8 => Result.ok b) ⟨xs,hxs⟩ = .ok ⟨xs,hxs⟩
  unfold Slice.clone List.clone
  split
  · rename_i ys he
    have hy : ys = xs := Result.ok.inj (he.symm.trans (mapM_id xs))
    cases hy
    rfl
  · rename_i e he
    have bad := he.symm.trans (mapM_id xs)
    cases bad
  · rename_i he
    have bad := he.symm.trans (mapM_id xs)
    cases bad

theorem u8_extend (v : alloc.vec.Vec U8) (s : Slice U8)
    (hb : v.val.length + s.val.length ≤ Usize.max) :
    ∃ out, alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = .ok out ∧
      out.val = v.val ++ s.val := extend_value _ v s hb (u8_clone s)

theorem extend_failure (v : alloc.vec.Vec U8) (s : Slice U8)
    (hb : ¬ v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = .fail Error.panic := by
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_neg hb]

#print axioms push_value
#print axioms extend_value
#print axioms mapM_id
#print axioms u8_clone
#print axioms u8_extend
#print axioms extend_failure
end PV_B3P_VecValue226
