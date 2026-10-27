import FJa_TensorMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_WeightPeriod
open FIv_NativeValue (K)
theorem add (cs : List K) (j t : Nat) :
    FJa_TensorMeaning.weight cs (j+2^cs.length*t)=FJa_TensorMeaning.weight cs j := by
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih =>
    have shift : 2^(c::cs).length*t=2^cs.length*(2*t) := by
      simp only [List.length_cons,pow_succ];ring
    rw [shift]
    unfold FJa_TensorMeaning.weight
    have hd : (j+2^cs.length*(2*t))/2^cs.length=j/2^cs.length+2*t := by
      rw [Nat.add_mul_div_left _ _ (by positivity)]
    rw [hd,ih (2*t)]
    simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,zero_mul,Nat.add_zero,Nat.mod_mod]
theorem mod (cs : List K) (j : Nat) :
    FJa_TensorMeaning.weight cs (j%2^cs.length)=FJa_TensorMeaning.weight cs j := by
  have h := add cs (j%2^cs.length) (j/2^cs.length)
  rw [Nat.mod_add_div] at h
  exact h.symm
#print axioms add
#print axioms mod
end AspisR1.FJa_WeightPeriod
end
