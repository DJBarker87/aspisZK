import Aeneas
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsExponentSteps
open Aeneas Aeneas.Std

theorem half_value (e : U64) : (U64.wrapping_shr e 1#u32).val = e.val/2 := by
  change (e.val >>> 1) = e.val/2
  exact Nat.shiftRight_eq_div_pow _ _

def steps : Nat → U64 → U64
  | 0,e => e
  | n+1,e => steps n (U64.wrapping_shr e 1#u32)

theorem value (n : Nat) (e : U64) : (steps n e).val = e.val/2^n := by
  induction n generalizing e with
  | zero => simp only [steps,Nat.pow_zero,Nat.div_one]
  | succ n ih =>
    simp only [steps,ih,half_value,Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm]

/-- Exponents from j%28 reach zero within five binary steps. -/
theorem five (e : U64) (h : e.val < 28) : steps 5 e = 0#u64 := by
  apply UScalar.eq_of_val_eq
  rw [value]
  change e.val/32 = 0
  exact Nat.div_eq_of_lt (by omega)
#print axioms half_value
#print axioms value
#print axioms five
end R1Z.PV_CB3_WeightsExponentSteps
