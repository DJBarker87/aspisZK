import FJj_PairTrace
set_option autoImplicit false
namespace AspisR1.FJj_SliceDivision
open Aeneas Aeneas.Std

theorem value (f : Slice U8) :
    ((Slice.len f).bv.udiv (32#usize).bv).toNat=f.val.length/32 := by
  rw [BitVec.toNat_udiv]
  change (Slice.len f).val/(32#usize).val=f.val.length/32
  rw [Slice.len_val]
  rfl
#print axioms value
end AspisR1.FJj_SliceDivision
