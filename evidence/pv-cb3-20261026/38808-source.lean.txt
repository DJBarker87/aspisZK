import R1Z.PV_CB3_WeightsSubtract
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsTensorIndex
open Aeneas Aeneas.Std Result

def index (kind : Usize) : Usize :=
  if kind < 4#usize then Usize.wrapping_sub kind 1#usize else Usize.wrapping_sub kind 2#usize

theorem bound (kind : Usize) (lo : 1 ≤ kind.val) (hi : kind.val < 7) : (index kind).val < 5 := by
  unfold index
  split_ifs with h
  · change kind.val < 4 at h
    rw [PV_CB3_WeightsSubtract.wrapping_value kind 1#usize (by exact lo)]
    change kind.val-1 < 5
    omega
  · change ¬kind.val < 4 at h
    rw [PV_CB3_WeightsSubtract.wrapping_value kind 2#usize (by change 2 ≤ kind.val; omega)]
    change kind.val-2 < 5
    omega

theorem checked (kind : Usize) (lo : 1 ≤ kind.val) :
    (if kind < 4#usize then UScalar.sub kind 1#usize else UScalar.sub kind 2#usize) = ok (index kind) := by
  unfold index
  split_ifs with h
  · exact PV_CB3_WeightsSubtract.checked kind 1#usize lo
  · apply PV_CB3_WeightsSubtract.checked
    change 2 ≤ kind.val
    change ¬kind.val < 4 at h
    omega
#print axioms bound
#print axioms checked
end R1Z.PV_CB3_WeightsTensorIndex
