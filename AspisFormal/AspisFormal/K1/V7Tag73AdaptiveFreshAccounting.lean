import AspisFormal.K1.V7Tag73FiniteSubkernel

/-!
# Adaptive fresh-answer accounting with a predictable charge

A policy may depend on its entire *already obtained* history. The next target
and raw subkernel are chosen by that policy before the next answer. Cached
steps consume no fresh draw. The source interpretation must establish these
facts: merely placing a completed execution in `State` does not establish them.

This file proves the adaptive calculation rather than postulating a global
probability inequality. A local potential can charge just a designated fresh
restoration instead of multiplying a bound by every node in the stored tree.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73AdaptiveFreshAccounting
open scoped BigOperators
open AspisK1.V7Tag73FiniteSubkernel
noncomputable section
variable {State Draw : Type*} [Fintype Draw] [DecidableEq Draw]

structure FreshNode (State Draw : Type*) where
  weight : Draw → ENNReal
  target : Finset Draw
  next : Draw → State
  charge : ENNReal

inductive ExposureStep (State Draw : Type*) where
  | halt
  | cached (next : State)
  | fresh (node : FreshNode State Draw)

/-- Expected continuation on non-hit answers only. -/
def safeWeighted (node : FreshNode State Draw) (f : State → ENNReal) : ENNReal :=
  weighted node.weight (fun d => if d ∈ node.target then 0 else f (node.next d))

/-- Bad-hit probability in an explicit finite-horizon decision process. -/
def firstHit (policy : State → ExposureStep State Draw) : Nat → State → ENNReal
  | 0, _ => 0
  | n + 1, s => match policy s with
    | .halt => 0
    | .cached next => firstHit policy n next
    | .fresh node => weighted node.weight
        (fun d => if d ∈ node.target then 1 else firstHit policy n (node.next d))

/-- Predictable cost spent up to and including the first hit. A charge of zero
is allowed for irrelevant fresh draws, but then local bad mass must be zero. -/
def expectedCharge (policy : State → ExposureStep State Draw) : Nat → State → ENNReal
  | 0, _ => 0
  | n + 1, s => match policy s with
    | .halt => 0
    | .cached next => expectedCharge policy n next
    | .fresh node => node.charge + safeWeighted node (expectedCharge policy n)

/-- Exact first-step event partition, not an independence assumption. -/
theorem fresh_hit_split (node : FreshNode State Draw) (f : State → ENNReal) :
    weighted node.weight (fun d => if d ∈ node.target then 1 else f (node.next d)) =
      eventMass node.weight (fun d => d ∈ node.target) + safeWeighted node f := by
  classical
  simp only [safeWeighted, weighted, eventMass]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d ∈ node.target <;> simp [hd]

theorem safeWeighted_mono (node : FreshNode State Draw) {f g : State → ENNReal}
    (h : ∀ s, f s ≤ g s) : safeWeighted node f ≤ safeWeighted node g := by
  apply weighted_mono
  intro d
  by_cases hd : d ∈ node.target <;> simp [hd, h]

theorem safeWeighted_scale (node : FreshNode State Draw) (c : ENNReal)
    (f : State → ENNReal) :
    safeWeighted node (fun s => c * f s) = c * safeWeighted node f := by
  unfold safeWeighted weighted
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d ∈ node.target
  · simp [hd]
  · simp only [hd, if_false]
    ac_rfl

/-- Adaptive first-hit bound. No common target across different histories is
required, and no division by eventual acceptance probability occurs. -/
theorem firstHit_le_error_mul_expectedCharge
    (policy : State → ExposureStep State Draw) (error : ENNReal)
    (localBound : ∀ s node, policy s = .fresh node →
      eventMass node.weight (fun d => d ∈ node.target) ≤ error * node.charge)
    (n : Nat) (s : State) :
    firstHit policy n s ≤ error * expectedCharge policy n s := by
  induction n generalizing s with
  | zero => simp [firstHit, expectedCharge]
  | succ n ih =>
      cases hs : policy s with
      | halt => simp [firstHit, expectedCharge, hs]
      | cached next => simpa [firstHit, expectedCharge, hs] using ih next
      | fresh node =>
          simp only [firstHit, expectedCharge, hs]
          change weighted node.weight
              (fun d => if d ∈ node.target then 1 else firstHit policy n (node.next d)) ≤
            error * (node.charge + safeWeighted node (expectedCharge policy n))
          rw [fresh_hit_split]
          calc
            eventMass node.weight (fun d => d ∈ node.target) +
                safeWeighted node (firstHit policy n) ≤
              error * node.charge +
                safeWeighted node (fun t => error * expectedCharge policy n t) :=
              add_le_add (localBound s node hs) (safeWeighted_mono node ih)
            _ = error * (node.charge + safeWeighted node (expectedCharge policy n)) := by
              rw [safeWeighted_scale, mul_add]

/-- Subprobability kernels make the hit mass a probability, even with abort. -/
theorem firstHit_le_one
    (policy : State → ExposureStep State Draw)
    (subprob : ∀ s node, policy s = .fresh node → ∑ d, node.weight d ≤ 1)
    (n : Nat) (s : State) : firstHit policy n s ≤ 1 := by
  induction n generalizing s with
  | zero => simp [firstHit]
  | succ n ih =>
      cases hs : policy s with
      | halt => simp [firstHit, hs]
      | cached next => simpa [firstHit, hs] using ih next
      | fresh node =>
          simp only [firstHit, hs]
          apply weighted_le node.weight (subprob s node hs) _ 1
          intro d
          by_cases hd : d ∈ node.target <;> simp [hd, ih]

/-- A local potential pays for each fresh step and its safe continuation.
This is the useful interface for a once-only marked restoration request. -/
theorem expectedCharge_le_potential
    (policy : State → ExposureStep State Draw) (potential : State → ENNReal)
    (cachedBudget : ∀ s next, policy s = .cached next → potential next ≤ potential s)
    (freshBudget : ∀ s node, policy s = .fresh node →
      node.charge + safeWeighted node potential ≤ potential s)
    (n : Nat) (s : State) : expectedCharge policy n s ≤ potential s := by
  induction n generalizing s with
  | zero => simp [expectedCharge]
  | succ n ih =>
      cases hs : policy s with
      | halt => simp [expectedCharge, hs]
      | cached next =>
          simpa [expectedCharge, hs] using (ih next).trans (cachedBudget s next hs)
      | fresh node =>
          simp only [expectedCharge, hs]
          exact (add_le_add le_rfl (safeWeighted_mono node ih)).trans
            (freshBudget s node hs)

/-- No all-stored-nodes union is forced by the abstract argument. A source
proof can supply a unit initial potential for a once-only predictable mark. -/
theorem firstHit_le_error_mul_potential
    (policy : State → ExposureStep State Draw) (error : ENNReal)
    (localBound : ∀ s node, policy s = .fresh node →
      eventMass node.weight (fun d => d ∈ node.target) ≤ error * node.charge)
    (potential : State → ENNReal)
    (cachedBudget : ∀ s next, policy s = .cached next → potential next ≤ potential s)
    (freshBudget : ∀ s node, policy s = .fresh node →
      node.charge + safeWeighted node potential ≤ potential s)
    (n : Nat) (s : State) : firstHit policy n s ≤ error * potential s := by
  exact (firstHit_le_error_mul_expectedCharge policy error localBound n s).trans
    (mul_le_mul_left'
      (expectedCharge_le_potential policy potential cachedBudget freshBudget n s) error)

/-- Sanity ceiling for unit-or-less charges. The potential theorem is usually
sharper; this bound must not silently replace a release budget. -/
theorem expectedCharge_le_horizon
    (policy : State → ExposureStep State Draw)
    (subprob : ∀ s node, policy s = .fresh node → ∑ d, node.weight d ≤ 1)
    (unitCharge : ∀ s node, policy s = .fresh node → node.charge ≤ 1)
    (n : Nat) (s : State) : expectedCharge policy n s ≤ (n : ENNReal) := by
  induction n generalizing s with
  | zero => simp [expectedCharge]
  | succ n ih =>
      cases hs : policy s with
      | halt => simp [expectedCharge, hs]
      | cached next =>
          simp only [expectedCharge, hs]
          exact (ih next).trans (by exact_mod_cast Nat.le_succ n)
      | fresh node =>
          simp only [expectedCharge, hs]
          have tail : safeWeighted node (expectedCharge policy n) ≤ (n : ENNReal) := by
            apply weighted_le node.weight (subprob s node hs) _ (n : ENNReal)
            intro d
            by_cases hd : d ∈ node.target
            · simp [hd]
            · simpa [hd] using ih (node.next d)
          calc
            node.charge + safeWeighted node (expectedCharge policy n) ≤ 1 + (n : ENNReal) :=
              add_le_add (unitCharge s node hs) tail
            _ = ((n + 1 : Nat) : ENNReal) := by simp [Nat.cast_add, add_comm]

#print axioms firstHit_le_error_mul_expectedCharge
#print axioms firstHit_le_one
#print axioms expectedCharge_le_potential
#print axioms firstHit_le_error_mul_potential
#print axioms expectedCharge_le_horizon
end
end AspisK1.V7Tag73AdaptiveFreshAccounting
