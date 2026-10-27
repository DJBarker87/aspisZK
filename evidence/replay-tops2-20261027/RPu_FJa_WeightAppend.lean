import RPu_FJa_TensorMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_WeightAppend
open FIv_NativeValue (K)
/-- The actual 6/4 split factors the SAME ten-coordinate tensor. -/
theorem value (xs ys : List K) (j : Nat) :
    FJa_TensorMeaning.weight (xs++ys) j=
      FJa_TensorMeaning.weight xs (j/2^ys.length)*FJa_TensorMeaning.weight ys j := by
  induction xs with
  | nil => simp only [List.nil_append,FJa_TensorMeaning.weight,one_mul]
  | cons c cs ih =>
    simp only [List.cons_append,FJa_TensorMeaning.weight,List.length_append,ih]
    have e : j/2^(cs.length+ys.length)=(j/2^ys.length)/2^cs.length := by
      rw [Nat.div_div_eq_div_mul,pow_add,Nat.mul_comm]
    rw [e]
    ring
#print axioms value
end AspisR1.FJa_WeightAppend
end
