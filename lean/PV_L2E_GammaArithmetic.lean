import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2E_GammaArithmetic

/-- Abstract-modulus law: all arithmetic automation sees variables, never a
large concrete power. This replaces the memory-heavy concrete gamma proof. -/
theorem cyclic (N l q a c out : Nat) (large : q+1<N)
    (low : l<N) (newlow : a<N) (carry : c≤1)
    (reconstruct : a+N*c=l+(q+1)) (restored : out=a+c) :
    out=(l+q)%(N-1)+1 := by
  have hc : c=0 ∨ c=1 := by omega
  rcases hc with rfl|rfl
  · simp only [Nat.mul_zero,Nat.add_zero] at reconstruct restored
    have h : l+q<N-1 := by omega
    rw [Nat.mod_eq_of_lt h]
    omega
  · simp only [Nat.mul_one] at reconstruct
    have hl : N-1≤l+q := by omega
    have hu : l+q-(N-1)<N-1 := by omega
    have hm : (l+q)%(N-1)=l+q-(N-1) := by
      calc
        (l+q)%(N-1)=((l+q-(N-1))+(N-1))%(N-1) := by rw [Nat.sub_add_cancel hl]
        _ = l+q-(N-1) := by
          simp only [Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
          exact Nat.mod_eq_of_lt hu
    rw [hm]
    omega

theorem carry_one (c : Nat) (upper : c≤1) (nonzero : c≠0) : c=1 := by omega

#print axioms cyclic
#print axioms carry_one
end PV_L2E_GammaArithmetic
