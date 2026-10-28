import PV_L2B_JointTransport
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
noncomputable section
namespace PV_L1_SamplerJoint
open PV_L2B_SamplerLaw

/-- Counts and errors remain in the SAME observation with the accepted value.
The observer may retain publication, initial history, and all preceding events.
The coefficients here are the IID-coordinate source kernel, not an assertion
that the native SHA or OS provider has this law. E1/E2 association remains P. -/
inductive Outcome (A : Type) where
  | accepted (draws : Nat) (value : A)
  | exhausted (draws : Nat)

def sourceKernel {A : Type} [Fintype A] (n : Nat) (q u : ℚ)
    (test : Outcome A → ℚ) : ℚ :=
  q^n*test (.exhausted n) +
    ∑ r ∈ Finset.range n, ∑ a : A, prefixMass q u r * test (.accepted (r+1) a)

def simulatorKernel {A : Type} [Fintype A] (n : Nat) (q p : ℚ)
    (test : Outcome A → ℚ) : ℚ :=
  q^n*test (.exhausted n) +
    ∑ r ∈ Finset.range n, geom q r * ((∑ a : A, test (.accepted (r+1) a))/p)

theorem complete_joint_kernel {A : Type} [Fintype A] (n : Nat) (q u p : ℚ)
    (hp : p ≠ 0) (normalization : u*p=1-q) (test : Outcome A → ℚ) :
    sourceKernel n q u test = simulatorKernel n q p test := by
  unfold sourceKernel simulatorKernel
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [prefix_uniform q u p r hp normalization]
  rw [← Finset.mul_sum]
  ring
#print axioms complete_joint_kernel

theorem scalar_joint_kernel (n p : Nat) (hp : 0<p)
    (test : Outcome (Fin p) → ℚ) :
    sourceKernel n (1/((p:ℚ)+1)) (1/((p:ℚ)+1)) test =
      simulatorKernel n (1/((p:ℚ)+1)) p test := by
  have hn : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have h1 : (p:ℚ)+1 ≠ 0 := by positivity
  exact complete_joint_kernel n _ _ (p:ℚ) hn (scalar_normalization _ h1) test
#print axioms scalar_joint_kernel

theorem geometric_sum (n : Nat) (q : ℚ) :
    (∑ r ∈ Finset.range n, geom q r) = 1-q^n := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,pow_zero,sub_self]
  | succ n ih => rw [Finset.sum_range_succ,ih,geom,pow_succ]; ring
#print axioms geometric_sum

theorem simulator_mass_one (n p : Nat) (q : ℚ) (hp : 0<p) :
    simulatorKernel n q p (fun _ : Outcome (Fin p) => 1) = 1 := by
  have hn : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold simulatorKernel
  simp only [mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,div_self hn]
  rw [geometric_sum]
  ring
#print axioms simulator_mass_one
end PV_L1_SamplerJoint
