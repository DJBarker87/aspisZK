import AspisR1DecodeKFullValueTrace
set_option autoImplicit false
namespace AspisR1.F3P_SliceIndex
open Aeneas Aeneas.Std Result

theorem read {A : Type} (s : Slice A) (i : Usize) (x : A)
    (h : Slice.index_usize s i=ok x) : s.val[i.val]?=some x := by
  unfold Slice.index_usize at h
  cases found : s.val[i.val]? with
  | none => simp [found] at h
  | some value =>
    simp only [found] at h
    exact congrArg some (Result.ok.inj h)

#print axioms read
end AspisR1.F3P_SliceIndex
