import NCJ_TensorDomains
import NCJ_CallLog
set_option autoImplicit false
namespace NCJ_TensorOffsets
open Aeneas Aeneas.Std AspisR1

def index (j n lane : Usize) : Usize := Usize.wrapping_add j (Usize.wrapping_mul lane n)

theorem value (n j lane : Usize) (hn : NCJ_TensorDomains.Stage n.val)
    (hj : j.val<n.val) (hl : lane.val<4) :
    (index j n lane).val=j.val+lane.val*n.val ∧
      (index j n lane).val<64 := by
  have bound:=NCJ_TensorDomains.write_bounds n.val j.val lane.val hn hj hl
  have hn16 : n.val≤16 := by rcases hn with h|h|h <;> omega
  have product : lane.val*n.val<64 := by
    have h:=Nat.mul_le_mul (show lane.val≤3 by omega) hn16
    omega
  have hm : lane.val*n.val<UScalar.size .Usize := by scalar_tac
  have hs : j.val+lane.val*n.val<UScalar.size .Usize := by scalar_tac
  have exactValue : (index j n lane).val=j.val+lane.val*n.val := by
    unfold index
    rw [Usize.wrapping_add_val_eq,Usize.wrapping_mul_val_eq,
      Nat.mod_eq_of_lt hm,Nat.mod_eq_of_lt hs]
  exact ⟨exactValue,by rw [exactValue];omega⟩

#print axioms value
end NCJ_TensorOffsets
