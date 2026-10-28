import Aeneas.Std
namespace PV_B3P_VecValue226
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem push_value (v : alloc.vec.Vec U8) (x : U8) (hb : v.val.length < Usize.max) :
    ∃ out, alloc.vec.Vec.push v x = .ok out ∧ out.val = v.val ++ [x] :=
  WP.spec_imp_exists (alloc.vec.Vec.push_spec v x hb)

theorem extend_value (inst : core.clone.Clone U8) (v : alloc.vec.Vec U8) (s : Slice U8)
    (hb : v.val.length + s.val.length ≤ Usize.max)
    (hc : Slice.clone inst.clone s = .ok s) :
    ∃ out, alloc.vec.Vec.extend_from_slice inst v s = .ok out ∧ out.val = v.val ++ s.val := by
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_pos hb,hc]
  exact ⟨_,rfl,rfl⟩

#print axioms push_value
#print axioms extend_value
#print List.clone
#print core.clone.CloneU8
#print core.clone.impls.CloneU8.clone
end PV_B3P_VecValue226
