import NCJ_TensorDomains
import FJj_TensorCell
set_option autoImplicit false
namespace NCJ_TensorOffsets
open Aeneas Aeneas.Std AspisR1

theorem value (n j lane : Usize) (hn : NCJ_TensorDomains.Stage n.val)
    (hj : j.val<n.val) (hl : lane.val<4) :
    (FJj_TensorCell.index j n lane).val=j.val+lane.val*n.val ∧
      (FJj_TensorCell.index j n lane).val<64 := by
  have bound:=NCJ_TensorDomains.write_bounds n.val j.val lane.val hn hj hl
  have hn16 : n.val≤16 := by rcases hn with h|h|h <;> omega
  have product : lane.val*n.val<64 := by
    have h:=Nat.mul_le_mul (show lane.val≤3 by omega) hn16
    omega
  have hm : lane.val*n.val<UScalar.size .Usize := by scalar_tac
  have hs : j.val+lane.val*n.val<UScalar.size .Usize := by scalar_tac
  have exactValue : (FJj_TensorCell.index j n lane).val=j.val+lane.val*n.val := by
    unfold FJj_TensorCell.index
    rw [Usize.wrapping_add_val_eq,Usize.wrapping_mul_val_eq,
      Nat.mod_eq_of_lt hm,Nat.mod_eq_of_lt hs]
  exact ⟨exactValue,by rw [exactValue];omega⟩

#print axioms value
end NCJ_TensorOffsets
