import PV_L2E_GammaTrace
set_option autoImplicit false
namespace PV_L2E_GammaValue
open PV_L2D_DivisionBounds PV_L2E_CarryValue PV_L2E_CarryTrace

/-- Complete value law for the two-pass cyclic increment. Both branches and
the second-pass restoration are retained; no concrete digit vector reduces. -/
theorem cyclic_increment (q : Nat) (ds : List Nat) (hq : q≤256)
    (width : ds.length=8) (hd : ∀ d∈ds,d<P) :
    value (PV_L2E_GammaTrace.run q ds).digits=(value ds+q)%(P^8-1)+1 := by
  have hb := value_bound ds hd
  rw [width] at hb
  have hp : 257<P^8 := by norm_num [P]
  have hr := reconstruct 0 (q+1) ds
  rw [width] at hr
  have hout := value_bound (run 0 (q+1) ds).1.1 (digit_bounds 0 (q+1) ds)
  rw [PV_L2E_CarryTrace.length,width] at hout
  by_cases hc : (run 0 (q+1) ds).1.2=0
  · rw [hc,Nat.mul_zero,Nat.add_zero] at hr
    have hs : value ds+q<P^8-1 := by omega
    simp only [PV_L2E_GammaTrace.run,hc,↓reduceIte]
    rw [Nat.mod_eq_of_lt hs]
    omega
  · have ha : q+1≤P := by dsimp [P]; omega
    have ne : ds≠[] := by intro h; simp [h] at width
    have hcarry := final_carry 0 (q+1) ds ha hd ne
    have he : (run 0 (q+1) ds).1.2=1 := by omega
    rw [he,Nat.mul_one] at hr
    have hz := PV_L2E_GammaTrace.second_carry_zero q ds hq width hd hc
    have ht := reconstruct 0 1 (run 0 (q+1) ds).1.1
    rw [hz,Nat.mul_zero,Nat.add_zero] at ht
    have hl : P^8-1≤value ds+q := by omega
    have hu : value ds+q<2*(P^8-1) := by omega
    have hm : (value ds+q)%(P^8-1)=value ds+q-(P^8-1) := by
      calc
        (value ds+q)%(P^8-1) = ((value ds+q-(P^8-1))+(P^8-1))%(P^8-1) := by
          rw [Nat.sub_add_cancel hl]
        _ = value ds+q-(P^8-1) := by
          simp only [Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by omega)
    simp only [PV_L2E_GammaTrace.run,hc,↓reduceIte]
    rw [hm]
    omega

#print axioms cyclic_increment
end PV_L2E_GammaValue
