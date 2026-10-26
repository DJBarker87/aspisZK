import R1Z.ProverRwEntropyUniform64
import R1Z.ProverRwEntropySum64
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropyTermination64
open ProverCommitPublicNonce40 ProverRwEntropyKernel64
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Distinct terminal outcomes. Payloads, partial writes and provider/event
state belong to C; they are not equated by these three constructor tags. -/
inductive Stop where
  | os | failed | diverged
  deriving DecidableEq, Fintype

def terminal {C : Type} [Fintype C]
    (stop : Stop → C → C → ℚ) (again : C → C → ℚ) (kind : Stop) : Nat → C → C → ℚ
  | 0,_,_ => 0
  | n+1,c,after => stop kind c after +
      ∑ middle : C, again c middle * terminal stop again kind n middle after

def exhaustion {C : Type} [Fintype C] (again : C → C → ℚ) : Nat → C → C → ℚ
  | 0,c,after => if c = after then 1 else 0
  | n+1,c,after => ∑ middle : C, again c middle * exhaustion again n middle after

def doneMass {C : Type} [Fintype C] (arrive : C → Private → C → ℚ)
    (again : C → C → ℚ) (fuel : Nat) (c : C) : ℚ :=
  ∑ secret : Private, marginal arrive again fuel c secret
def stopMass {C : Type} [Fintype C] (stop : Stop → C → C → ℚ)
    (again : C → C → ℚ) (fuel : Nat) (c : C) : ℚ :=
  ∑ kind : Stop, ∑ after : C, terminal stop again kind fuel c after
def zeroMass {C : Type} [Fintype C] (again : C → C → ℚ) (fuel : Nat) (c : C) : ℚ :=
  ∑ after : C, exhaustion again fuel c after

def doneHead {C : Type} [Fintype C] (arrive : C → Private → C → ℚ) (c : C) : ℚ :=
  ∑ secret : Private, ∑ after : C, arrive c secret after
def stopHead {C : Type} [Fintype C] (stop : Stop → C → C → ℚ) (c : C) : ℚ :=
  ∑ kind : Stop, ∑ after : C, stop kind c after

theorem done_step {C : Type} [Fintype C] (arrive : C → Private → C → ℚ)
    (again : C → C → ℚ) (fuel : Nat) (c : C) :
    doneMass arrive again (fuel+1) c = doneHead arrive c +
      ∑ middle : C, again c middle * doneMass arrive again fuel middle := by
  unfold doneMass doneHead
  simp_rw [marginal_step]
  rw [Finset.sum_add_distrib]
  exact congrArg (fun tail : ℚ => (∑ secret : Private, ∑ after : C, arrive c secret after) + tail)
    (ProverRwEntropySum64.swap_weighted_sum (again c)
      (fun secret middle => marginal arrive again fuel middle secret))

theorem terminal_step {C : Type} [Fintype C] (stop : Stop → C → C → ℚ)
    (again : C → C → ℚ) (kind : Stop) (fuel : Nat) (c : C) :
    (∑ after : C, terminal stop again kind (fuel+1) c after) =
      (∑ after : C, stop kind c after) +
      ∑ middle : C, again c middle * ∑ after : C, terminal stop again kind fuel middle after := by
  simp only [terminal,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro middle _
  rw [Finset.mul_sum]

theorem stop_step {C : Type} [Fintype C] (stop : Stop → C → C → ℚ)
    (again : C → C → ℚ) (fuel : Nat) (c : C) :
    stopMass stop again (fuel+1) c = stopHead stop c +
      ∑ middle : C, again c middle * stopMass stop again fuel middle := by
  unfold stopMass stopHead
  simp_rw [terminal_step]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro middle _
  rw [Finset.mul_sum]

theorem zero_step {C : Type} [Fintype C]
    (again : C → C → ℚ) (fuel : Nat) (c : C) :
    zeroMass again (fuel+1) c =
      ∑ middle : C, again c middle * zeroMass again fuel middle := by
  unfold zeroMass
  simp only [exhaustion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro middle _
  rw [Finset.mul_sum]

/-- Exact mass partition, retaining OS, extraction failure, divergence and
zero exhaustion. normalized is ordinary one-step probability conservation;
it is not an availability bound or a whole native-source refinement. -/
theorem conservation {C : Type} [Fintype C]
    (arrive : C → Private → C → ℚ) (stop : Stop → C → C → ℚ) (again : C → C → ℚ)
    (normalized : ∀ c, doneHead arrive c + stopHead stop c + (∑ middle : C, again c middle) = 1)
    (fuel : Nat) (c : C) :
    doneMass arrive again fuel c + stopMass stop again fuel c + zeroMass again fuel c = 1 := by
  induction fuel generalizing c with
  | zero => simp [doneMass,marginal,output,stopMass,terminal,zeroMass,exhaustion]
  | succ fuel ih =>
    rw [done_step,stop_step,zero_step]
    calc
      _ = doneHead arrive c + stopHead stop c + ∑ middle : C, again c middle *
          (doneMass arrive again fuel middle + stopMass stop again fuel middle + zeroMass again fuel middle) := by
        simp only [mul_add,Finset.sum_add_distrib]
        ring
      _ = doneHead arrive c + stopHead stop c + (∑ middle : C, again c middle) := by
        simp only [ih,mul_one]
      _ = 1 := normalized c

#print axioms done_step
#print axioms terminal_step
#print axioms stop_step
#print axioms zero_step
#print axioms conservation
end R1Z.ProverRwEntropyTermination64
