import AspisR1DecodeKFullValueTrace
set_option autoImplicit false
namespace AspisR1.F3P_SliceIndex
open Aeneas Aeneas.Std Result

theorem read {A : Type} (s : Slice A) (i : Usize) (x : A)
    (h : Slice.index_usize s i=ok x) : s.val[i.val]?=some x := by
  unfold Slice.index_usize at h
  split at h
  · cases h
  · rename_i value hv
    cases Result.ok.inj h
    exact hv


#print axioms read
end AspisR1.F3P_SliceIndex
