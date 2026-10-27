import FJa_ExpandModel
import FJa_FoldPoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_TensorMeaning
open FIv_NativeValue (K)
/-- Leading coordinate is the highest bit, exactly matching installed
successive adjacent-child writes. -/
def weight : List K → Nat → K
  | [],_ => 1
  | c::cs,j => (if j/2^cs.length%2=0 then 1-c else c)*weight cs j
/-- Symbolic literal tensor meaning for any live width and input mass. -/
theorem value (cs : List K) (n : Nat) (f : Nat → K) (j : Nat)
    (hj : j<2^cs.length*n) :
    FJa_ExpandModel.value cs n f j=f (j/2^cs.length)*weight cs j := by
  induction cs generalizing n f with
  | nil => simp only [FJa_ExpandModel.value,weight,List.length_nil,pow_zero,Nat.div_one,mul_one]
  | cons c cs ih =>
    have hb : j<2^cs.length*(2*n) := by
      simpa only [List.length_cons,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hj
    rw [FJa_ExpandModel.value,ih (2*n) (FJa_SplitModel.fold c n f) hb]
    have hi : j/2^cs.length<2*n := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      simpa only [Nat.mul_comm] using hb
    rw [FJa_FoldPoint.value c f n _ hi]
    simp only [weight,List.length_cons,pow_succ,Nat.div_div_eq_div_mul]
    ring
#print axioms value
end AspisR1.FJa_TensorMeaning
end
