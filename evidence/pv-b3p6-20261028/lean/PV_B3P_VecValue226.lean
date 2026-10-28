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
  rw [dif_pos hb]
  simp only [hc]
  exact ⟨_,rfl,rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem u8_clone (s : Slice U8) : Slice.clone core.clone.CloneU8.clone s = .ok s := by
  change Slice.clone (fun b : U8 => Result.ok b) s = .ok s
  have hm : List.mapM (fun b : U8 => Result.ok b) s.val = .ok s.val := by simp
  unfold Slice.clone List.clone
  simp only [hm,bind_tc_ok]
  apply congrArg Result.ok
  apply Subtype.ext
  rfl

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
#print axioms u8_clone
#print axioms u8_extend
#print axioms extend_failure
end PV_B3P_VecValue226
