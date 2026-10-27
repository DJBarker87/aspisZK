import FJc_S2Rows
import FJg_TensorDigits
import R1D18Transport
set_option autoImplicit false
namespace AspisR1.FJr_InactiveRowIndex

theorem value (i : Fin 64) (s t : Fin 4) :
    rowNat (childIndex (childIndex i s) t).val=FJc_S2Rows.row i.val (4*s.val+t.val) := by
  have hi := i.isLt
  have hs := s.isLt
  have ht := t.isLt
  have h0 : (childIndex (childIndex i s) t).val%4=t.val := by
    dsimp only [childIndex]
    omega
  have h1 : (childIndex (childIndex i s) t).val/4%4=s.val := by
    dsimp only [childIndex]
    omega
  have h2 : (childIndex (childIndex i s) t).val/16%4=i.val%4 := by
    dsimp only [childIndex]
    omega
  have h3 : (childIndex (childIndex i s) t).val/64%4=i.val/4%4 := by
    dsimp only [childIndex]
    omega
  have h4 : (childIndex (childIndex i s) t).val/256%4=i.val/16 := by
    dsimp only [childIndex]
    omega
  unfold rowNat FJc_S2Rows.row
  rw [h0,h1,h2,h3,h4]
  have low0 : (4*s.val+t.val)%4=t.val := by omega
  have low1 : (4*s.val+t.val)/4=s.val := by omega
  rw [low0,low1,Nat.mul_comm 16 (i.val%4)]

#print axioms value
end AspisR1.FJr_InactiveRowIndex
