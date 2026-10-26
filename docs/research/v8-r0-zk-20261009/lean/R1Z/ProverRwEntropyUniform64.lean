import R1Z.ProverRwEntropyKernel64
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropyUniform64
open ProverCommitPublicNonce40 ProverRwEntropyKernel64
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def oneSecret : Private :=
  ⟨fun _ _ => 1,by
    intro i eq
    have h := congrFun eq 0
    exact (by decide : (1 : UInt8) ≠ 0) h⟩

/-- A finite constant subdistribution factors by its total mass. No
conditioning on a positive success probability is required. -/
theorem constant_factor {X : Type} [Fintype X] [Nonempty X]
    (weight : X → ℚ) (same : ∀ x y, weight x = weight y) (x : X) :
    weight x = (∑ y : X, weight y) / (Fintype.card X : ℚ) := by
  have total : (∑ y : X, weight y) = (Fintype.card X : ℚ) * weight x := by
    calc
      (∑ y : X, weight y) = ∑ _y : X, weight x :=
        Finset.sum_congr rfl (fun y _ => same y x)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have card : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (eq_div_iff card).mpr
  rw [total]
  ring

def successMass {C : Type} [Fintype C]
    (available : C → ℚ) (law : C → Raw → ℚ) (next : C → Raw → C → ℚ)
    (fuel : Nat) (c : C) : ℚ :=
  ∑ secret : Private, marginal (arrival available law next) (retry available law next) fuel c secret

/-- Exact successful-output mass: aborts stay in the missing successMass,
which may be zero. The joint post-context remains in output; this theorem
does not make it independent of the returned secret. -/
theorem success_factor {C : Type} [Fintype C]
    (available : C → ℚ) (law : C → Raw → ℚ) (next : C → Raw → C → ℚ)
    (entropy_law : E1 law) (transition : ∀ c raw, ∑ after : C, next c raw after = 1)
    (fuel : Nat) (c : C) (secret : Private) :
    marginal (arrival available law next) (retry available law next) fuel c secret =
      successMass available law next fuel c / (Fintype.card Private : ℚ) := by
  letI : Nonempty Private := ⟨oneSecret⟩
  exact constant_factor _
    (fun x y => output_uniform available law next entropy_law transition fuel c x y) secret

/-- The selected sixteen-draw algorithm, with all provider contexts retained
by the joint kernel above. This remains an E1 model theorem, not native adequacy. -/
theorem sixteen_factor {C : Type} [Fintype C]
    (available : C → ℚ) (law : C → Raw → ℚ) (next : C → Raw → C → ℚ)
    (entropy_law : E1 law) (transition : ∀ c raw, ∑ after : C, next c raw after = 1)
    (c : C) (secret : Private) :
    marginal (arrival available law next) (retry available law next) 16 c secret =
      successMass available law next 16 c / (Fintype.card Private : ℚ) :=
  success_factor available law next entropy_law transition 16 c secret

#print axioms constant_factor
#print axioms success_factor
#print axioms sixteen_factor
end R1Z.ProverRwEntropyUniform64
