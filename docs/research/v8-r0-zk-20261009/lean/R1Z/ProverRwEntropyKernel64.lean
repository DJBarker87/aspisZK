import R1Z.ProverRwEntropyAbort64
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropyKernel64
open ProverCommitPublicNonce40
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Availability can depend on the complete entered context. next retains
the provider, partial/full reply and ordered history in its post-context.
It may depend arbitrarily on the returned raw bytes. -/
def arrival {C : Type} (available : C → ℚ) (law : C → Raw → ℚ)
    (next : C → Raw → C → ℚ) (c : C) (secret : Private) (after : C) : ℚ :=
  available c * law c secret.val * next c secret.val after

def retry {C : Type} [Fintype C] (available : C → ℚ) (law : C → Raw → ℚ)
    (next : C → Raw → C → ℚ) (c after : C) : ℚ :=
  ∑ raw : Raw, if decode raw = none then available c * law c raw * next c raw after else 0

/-- Joint successful-output/post-context mass. No post-state independence
is imposed, and no histories are reset at a rejected candidate. -/
def output {C : Type} [Fintype C]
    (arrive : C → Private → C → ℚ) (again : C → C → ℚ) : Nat → C → Private → C → ℚ
  | 0,_,_,_ => 0
  | n+1,c,secret,after => arrive c secret after +
      ∑ middle : C, again c middle * output arrive again n middle secret after

def marginal {C : Type} [Fintype C]
    (arrive : C → Private → C → ℚ) (again : C → C → ℚ)
    (fuel : Nat) (c : C) (secret : Private) : ℚ :=
  ∑ after : C, output arrive again fuel c secret after

theorem marginal_step {C : Type} [Fintype C]
    (arrive : C → Private → C → ℚ) (again : C → C → ℚ)
    (fuel : Nat) (c : C) (secret : Private) :
    marginal arrive again (fuel+1) c secret = (∑ after : C, arrive c secret after) +
      ∑ middle : C, again c middle * marginal arrive again fuel middle secret := by
  unfold marginal
  simp only [output,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro middle _
  rw [Finset.mul_sum]

/-- Exactly the existing named E1, not a new uniformity assumption. next's
normalization describes a conditional state transition, not independent coins. -/
theorem e1_arrival {C : Type} [Fintype C]
    (available : C → ℚ) (law : C → Raw → ℚ) (next : C → Raw → C → ℚ)
    (entropy_law : E1 law) (transition : ∀ c raw, ∑ after : C, next c raw after = 1)
    (c : C) (secret : Private) :
    (∑ after : C, arrival available law next c secret after) =
      available c / (Fintype.card Raw : ℚ) := by
  unfold arrival
  rw [← Finset.mul_sum,transition,mul_one,entropy_law]
  ring

/-- Successful seed marginals are equal after any bounded number of draws,
even with context-dependent availability and byte-dependent provider updates.
This is not independence from the returned state or an actual native binding. -/
theorem output_uniform {C : Type} [Fintype C]
    (available : C → ℚ) (law : C → Raw → ℚ) (next : C → Raw → C → ℚ)
    (entropy_law : E1 law) (transition : ∀ c raw, ∑ after : C, next c raw after = 1)
    (fuel : Nat) (c : C) (x y : Private) :
    marginal (arrival available law next) (retry available law next) fuel c x =
      marginal (arrival available law next) (retry available law next) fuel c y := by
  induction fuel generalizing c with
  | zero => simp only [marginal,output,Finset.sum_const_zero]
  | succ fuel ih =>
    rw [marginal_step,marginal_step,
      e1_arrival available law next entropy_law transition,
      e1_arrival available law next entropy_law transition]
    congr 1
    apply Finset.sum_congr rfl
    intro middle _
    rw [ih middle]

#print axioms marginal_step
#print axioms e1_arrival
#print axioms output_uniform
end R1Z.ProverRwEntropyKernel64
