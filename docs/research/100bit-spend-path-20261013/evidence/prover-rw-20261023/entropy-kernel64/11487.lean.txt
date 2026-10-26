import R1Z.ProverRwEntropyTermination64
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropyKernelBounds64
open ProverRwEntropyTermination64
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- A bound at every entered context replaces an independence assumption.
The joint terminal/post-state kernels are not erased by this marginal bound. -/
theorem zero_bound {C : Type} [Fintype C] (again : C → C → ℚ) (δ : ℚ)
    (δnonneg : 0 ≤ δ) (positive : ∀ c after, 0 ≤ again c after)
    (row : ∀ c, (∑ after : C, again c after) ≤ δ) (fuel : Nat) (c : C) :
    zeroMass again fuel c ≤ δ^fuel := by
  induction fuel generalizing c with
  | zero => simp [zeroMass,exhaustion]
  | succ fuel ih =>
    rw [zero_step]
    calc
      (∑ middle : C, again c middle * zeroMass again fuel middle) ≤
          ∑ middle : C, again c middle * δ^fuel :=
        Finset.sum_le_sum (fun middle _ => mul_le_mul_of_nonneg_left (ih middle) (positive c middle))
      _ = (∑ middle : C, again c middle) * δ^fuel := (Finset.sum_mul _ _ _).symm
      _ ≤ δ * δ^fuel := mul_le_mul_of_nonneg_right (row c) (pow_nonneg δnonneg _)
      _ = δ^(fuel+1) := by rw [pow_succ]; ring

/-- The outer kernel advances only after a rejected body. Its context may
carry that body's entire secret-dependent state and oracle/observer history. -/
def campaign {C : Type} [Fintype C] (hazard : C → ℚ) (again : C → C → ℚ) : Nat → C → ℚ
  | 0,_ => 0
  | n+1,c => hazard c + ∑ after : C, again c after * campaign hazard again n after

theorem campaign_bound {C : Type} [Fintype C]
    (hazard : C → ℚ) (again : C → C → ℚ) (δ : ℚ) (δnonneg : 0 ≤ δ)
    (positive : ∀ c after, 0 ≤ again c after) (row : ∀ c, (∑ after : C, again c after) ≤ 1)
    (bound : ∀ c, hazard c ≤ δ) (fuel : Nat) (c : C) :
    campaign hazard again fuel c ≤ (fuel : ℚ)*δ := by
  induction fuel generalizing c with
  | zero => simp only [campaign,Nat.cast_zero,zero_mul,le_refl]
  | succ fuel ih =>
    rw [campaign]
    have tail : (∑ after : C, again c after * campaign hazard again fuel after) ≤ (fuel : ℚ)*δ := by
      calc
        _ ≤ ∑ after : C, again c after * ((fuel : ℚ)*δ) :=
          Finset.sum_le_sum (fun after _ => mul_le_mul_of_nonneg_left (ih after) (positive c after))
        _ = (∑ after : C, again c after) * ((fuel : ℚ)*δ) := (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * ((fuel : ℚ)*δ) := mul_le_mul_of_nonneg_right (row c)
          (mul_nonneg (Nat.cast_nonneg _) δnonneg)
        _ = _ := one_mul _
    have sum := add_le_add (bound c) tail
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using sum

theorem eight_bound {C : Type} [Fintype C]
    (hazard : C → ℚ) (again : C → C → ℚ) (δ : ℚ) (δnonneg : 0 ≤ δ)
    (positive : ∀ c after, 0 ≤ again c after) (row : ∀ c, (∑ after : C, again c after) ≤ 1)
    (bound : ∀ c, hazard c ≤ δ) (c : C) :
    campaign hazard again 8 c ≤ 8*δ := by
  exact campaign_bound hazard again δ δnonneg positive row bound 8 c

#print axioms zero_bound
#print axioms campaign_bound
#print axioms eight_bound
end R1Z.ProverRwEntropyKernelBounds64
