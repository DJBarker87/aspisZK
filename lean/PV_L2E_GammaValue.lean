import PV_L2E_GammaTrace
import PV_L2E_GammaArithmetic
set_option autoImplicit false
namespace PV_L2E_GammaValue
open PV_L2D_DivisionBounds PV_L2E_CarryValue PV_L2E_CarryTrace

/-- Complete value law. The large power is passed to an abstract arithmetic
lemma; the kernel never normalizes a concrete recurrence or digit vector. -/
theorem cyclic_increment (q : Nat) (ds : List Nat) (hq : q≤256)
    (width : ds.length=8) (hd : ∀ d∈ds,d<P) :
    value (PV_L2E_GammaTrace.run q ds).digits=(value ds+q)%(P^8-1)+1 := by
  have hb := value_bound ds hd
  rw [width] at hb
  have hp : 257<P^8 := by norm_num [P]
  have hsmall : q+1<P^8 := lt_of_le_of_lt (Nat.add_le_add_right hq 1) hp
  have hr := reconstruct 0 (q+1) ds
  rw [width] at hr
  have hout := value_bound (run 0 (q+1) ds).1.1 (digit_bounds 0 (q+1) ds)
  rw [PV_L2E_CarryTrace.length,width] at hout
  have ha : q+1≤P := le_trans (Nat.add_le_add_right hq 1) (by decide : 257≤P)
  have ne : ds≠[] := by intro h; simp [h] at width
  have hcarry := final_carry 0 (q+1) ds ha hd ne
  have restored : value (PV_L2E_GammaTrace.run q ds).digits=
      value (run 0 (q+1) ds).1.1+(run 0 (q+1) ds).1.2 := by
    by_cases hc : (run 0 (q+1) ds).1.2=0
    · simp only [PV_L2E_GammaTrace.run,hc,↓reduceIte,Nat.add_zero]
    · have he := PV_L2E_GammaArithmetic.carry_one _ hcarry hc
      have hz := PV_L2E_GammaTrace.second_carry_zero q ds hq width hd hc
      have ht := reconstruct 0 1 (run 0 (q+1) ds).1.1
      rw [hz,Nat.mul_zero,Nat.add_zero] at ht
      simp only [PV_L2E_GammaTrace.run,hc,↓reduceIte,he]
      exact ht
  exact PV_L2E_GammaArithmetic.cyclic _ _ _ _ _ _ hsmall hb hout hcarry hr restored

#print axioms cyclic_increment
end PV_L2E_GammaValue
