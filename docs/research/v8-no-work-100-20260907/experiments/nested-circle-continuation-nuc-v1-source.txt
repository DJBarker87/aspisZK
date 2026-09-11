import RootSetPairMass

/-! Continuation-valued circle3/distinct3 payment. Final history is retained
through all duplicate retries; ordinary failure and exhausted retries pay
zero. Structural domination uses no freshness law or independent labels.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.NestedCircleContinuation
open Finset
open AspisV8.JointImageGame AspisV8.RelationCompatibleMoment
open AspisV8.NestedCircleMass.Generic
noncomputable section
local instance decision (p : Prop) : Decidable p := Classical.propDecidable p

namespace Generic
variable {O H V : Type*} [DecidableEq V]

theorem pay_zero (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (n : Nat) (h : H) :
    pay coins draw accept n h (fun _ _ => 0) = 0 := by
  have zero := pay_scale coins draw accept n h (fun _ _ => 0) 0
  simpa only [mul_zero] using zero

theorem pay_mono (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (n : Nat)
    (f g : V → H → ℚ) (bounded : ∀ v next, accept v → f v next ≤ g v next) (h : H) :
    pay coins draw accept n h f ≤ pay coins draw accept n h g := by
  induction n generalizing h with
  | zero => exact le_rfl
  | succ n ih =>
      apply avg_mono
      intro coin member
      cases result : draw h coin with
      | none => simp only [result, le_refl]
      | some pair =>
          rcases pair with ⟨value, next⟩
          by_cases good : accept value
          · simpa only [result, if_pos good] using bounded value next good
          · simpa only [result, if_neg good] using ih next

theorem pay_le_constant (coins : Finset O) (nonempty : coins.Nonempty)
    (draw : H → O → Option (V × H)) (accept : V → Prop) [DecidablePred accept]
    (n : Nat) (f : V → H → ℚ) (b : ℚ) (nonnegative : 0 ≤ b)
    (bounded : ∀ v next, accept v → f v next ≤ b) (h : H) :
    pay coins draw accept n h f ≤ b := by
  induction n generalizing h with
  | zero => exact nonnegative
  | succ n ih =>
      apply avg_le coins nonempty
      intro coin member
      cases result : draw h coin with
      | none => simpa only [result] using nonnegative
      | some pair =>
          rcases pair with ⟨value, next⟩
          by_cases good : accept value
          · simpa only [result, if_pos good] using bounded value next good
          · simpa only [result, if_neg good] using ih next

theorem pay_sum {I : Type*} (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (n : Nat) (h : H)
    (S : Finset I) (f : I → V → H → ℚ) :
    pay coins draw accept n h (fun v next => ∑ i ∈ S, f i v next) =
      ∑ i ∈ S, pay coins draw accept n h (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, pay_zero]
  | @insert i S absent ih =>
      simp only [Finset.sum_insert absent, pay_add, ih]

/-- Duplicate success alone retries the outer distinct sampler. Its
updated history is retained; failure inside a circle call pays zero. -/
def distinctPay (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (first : V) :
    Nat → H → (V → H → ℚ) → ℚ
  | 0, _, _ => 0
  | n+1, h, reward => pay coins draw accept 3 h (fun value next =>
      if value = first then distinctPay coins draw accept first n next reward
      else reward value next)

theorem distinctPay_zero (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (first : V) (n : Nat) (h : H) :
    distinctPay coins draw accept first n h (fun _ _ => 0) = 0 := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp only [distinctPay, ih, ite_self, pay_zero]

theorem distinctPay_mono (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (first : V) (n : Nat)
    (f g : V → H → ℚ)
    (bounded : ∀ v next, accept v → v ≠ first → f v next ≤ g v next) (h : H) :
    distinctPay coins draw accept first n h f ≤ distinctPay coins draw accept first n h g := by
  induction n generalizing h with
  | zero => exact le_rfl
  | succ n ih =>
      apply pay_mono
      intro value next good
      by_cases same : value = first
      · simpa only [if_pos same] using ih next
      · simpa only [if_neg same] using bounded value next good same

theorem distinctPay_le_constant (coins : Finset O) (nonempty : coins.Nonempty)
    (draw : H → O → Option (V × H)) (accept : V → Prop) [DecidablePred accept]
    (first : V) (n : Nat) (f : V → H → ℚ) (b : ℚ) (nonnegative : 0 ≤ b)
    (bounded : ∀ v next, accept v → v ≠ first → f v next ≤ b) (h : H) :
    distinctPay coins draw accept first n h f ≤ b := by
  induction n generalizing h with
  | zero => exact nonnegative
  | succ n ih =>
      apply pay_le_constant coins nonempty draw accept 3 _ b nonnegative
      intro value next good
      by_cases same : value = first
      · simpa only [if_pos same] using ih next
      · simpa only [if_neg same] using bounded value next good same

theorem distinctPay_add (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (first : V) (n : Nat) (h : H)
    (f g : V → H → ℚ) :
    distinctPay coins draw accept first n h (fun v next => f v next + g v next) =
      distinctPay coins draw accept first n h f + distinctPay coins draw accept first n h g := by
  induction n generalizing h with
  | zero => simp only [distinctPay, zero_add]
  | succ n ih =>
      simp only [distinctPay]
      rw [← pay_add]
      apply pay_congr
      intro value next
      by_cases same : value = first
      · simp only [if_pos same, ih]
      · simp only [if_neg same]

theorem distinctPay_sum {I : Type*} (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (first : V) (n : Nat) (h : H)
    (S : Finset I) (f : I → V → H → ℚ) :
    distinctPay coins draw accept first n h (fun v next => ∑ i ∈ S, f i v next) =
      ∑ i ∈ S, distinctPay coins draw accept first n h (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, distinctPay_zero]
  | @insert i S absent ih => simp only [Finset.sum_insert absent, distinctPay_add, ih]

theorem distinctPay_target (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (first target : V) (n : Nat) (h : H) :
    distinctPay coins draw accept first n h (fun v _ => if v = target then 1 else 0) =
      distinct coins draw accept first target n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp only [distinctPay, distinct, ih]

/-- The final callback sees both parameters and the actual terminal history.
The between-first/second update is applied once, before distinct retries. -/
def pairPay (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (between : V → H → H)
    (reward : V → V → H → ℚ) (h : H) : ℚ :=
  pay coins draw accept 3 h (fun first next =>
    distinctPay coins draw accept first 3 (between first next) (reward first))

theorem pairPay_mono (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (between : V → H → H)
    (f g : V → V → H → ℚ)
    (bounded : ∀ first second next, accept first → accept second → second ≠ first →
      f first second next ≤ g first second next) (h : H) :
    pairPay coins draw accept between f h ≤ pairPay coins draw accept between g h := by
  apply pay_mono
  intro first next goodFirst
  exact distinctPay_mono coins draw accept first 3 (f first) (g first)
    (fun second terminal goodSecond different =>
      bounded first second terminal goodFirst goodSecond different) (between first next)

theorem pairPay_le_constant (coins : Finset O) (nonempty : coins.Nonempty)
    (draw : H → O → Option (V × H)) (accept : V → Prop) [DecidablePred accept]
    (between : V → H → H) (f : V → V → H → ℚ) (b : ℚ) (nonnegative : 0 ≤ b)
    (bounded : ∀ first second next, accept first → accept second → second ≠ first →
      f first second next ≤ b) (h : H) : pairPay coins draw accept between f h ≤ b := by
  apply pay_le_constant coins nonempty draw accept 3 _ b nonnegative
  intro first next goodFirst
  exact distinctPay_le_constant coins nonempty draw accept first 3 (f first) b nonnegative
    (fun second terminal goodSecond different =>
      bounded first second terminal goodFirst goodSecond different) (between first next)

theorem pairPay_add (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (between : V → H → H)
    (f g : V → V → H → ℚ) (h : H) :
    pairPay coins draw accept between (fun v w next => f v w next + g v w next) h =
      pairPay coins draw accept between f h + pairPay coins draw accept between g h := by
  simp only [pairPay, distinctPay_add, pay_add]

theorem pairPay_sum {I : Type*} (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (between : V → H → H)
    (S : Finset I) (f : I → V → V → H → ℚ) (h : H) :
    pairPay coins draw accept between (fun v w next => ∑ i ∈ S, f i v w next) h =
      ∑ i ∈ S, pairPay coins draw accept between (f i) h := by
  simp only [pairPay, distinctPay_sum, pay_sum]

theorem pairPay_target (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (between : V → H → H)
    (first target : V) (h : H) :
    pairPay coins draw accept between (fun v w _ =>
      if v = first ∧ w = target then 1 else 0) h =
        orderedPair coins draw accept between first target h := by
  unfold pairPay orderedPair
  apply pay_congr
  intro value next
  by_cases same : value = first
  · subst value
    simp only [true_and, if_pos rfl, distinctPay_target]
  · simp only [same, false_and, if_false, distinctPay_zero, if_neg same]

theorem pair_indicator_sum (S : Finset V) (first second : V) :
    (if (first, second) ∈ S.offDiag then (1 : ℚ) else 0) =
      ∑ pair ∈ S.offDiag, if first = pair.1 ∧ second = pair.2 then (1 : ℚ) else 0 := by
  classical
  have coordinate (pair : V × V) :
      (first = pair.1 ∧ second = pair.2) ↔ pair = (first, second) := by
    constructor
    · rintro ⟨one, two⟩
      exact Prod.ext one.symm two.symm
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp_rw [coordinate]
  simp

/-- No law is used: finite linearity identifies the exact root-indicator
payment with the existing ordered-target-pair sum. -/
theorem pairPay_indicator (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (between : V → H → H)
    (S : Finset V) (h : H) :
    pairPay coins draw accept between
      (fun first second _ => if (first, second) ∈ S.offDiag then 1 else 0) h =
        ∑ pair ∈ S.offDiag, orderedPair coins draw accept between pair.1 pair.2 h := by
  simp_rw [pair_indicator_sum]
  rw [pairPay_sum]
  apply Finset.sum_congr rfl
  intro pair member
  exact pairPay_target coins draw accept between pair.1 pair.2 h

/-- Arbitrary terminal-history continuation dominated by the root-pair
indicator. Nonnegativity is not needed for this upper-bound direction. -/
theorem pairPay_root_domination (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (between : V → H → H)
    (S : Finset V) (reward : V → V → H → ℚ)
    (bounded : ∀ first second next, accept first → accept second → second ≠ first →
      reward first second next ≤ if (first, second) ∈ S.offDiag then 1 else 0) (h : H) :
    pairPay coins draw accept between reward h ≤
      ∑ pair ∈ S.offDiag, orderedPair coins draw accept between pair.1 pair.2 h :=
  (pairPay_mono coins draw accept between reward _ bounded h).trans_eq
    (pairPay_indicator coins draw accept between S h)

/-- Used for the later gamma slice: exceptional histories cost their
actual pair-root mass, while every nonexceptional continuation costs at
most the same nonnegative b. Abort histories never acquire a continuation. -/
theorem pairPay_exception_bound (coins : Finset O) (nonempty : coins.Nonempty)
    (draw : H → O → Option (V × H)) (accept : V → Prop) [DecidablePred accept]
    (between : V → H → H) (S : Finset V) (reward : V → V → H → ℚ)
    (b : ℚ) (nonnegative : 0 ≤ b)
    (bounded : ∀ first second next, accept first → accept second → second ≠ first →
      reward first second next ≤ (if (first, second) ∈ S.offDiag then 1 else 0) + b) (h : H) :
    pairPay coins draw accept between reward h ≤
      (∑ pair ∈ S.offDiag, orderedPair coins draw accept between pair.1 pair.2 h) + b := by
  have bound := pairPay_mono coins draw accept between reward _ bounded h
  rw [pairPay_add, pairPay_indicator] at bound
  have constant := pairPay_le_constant coins nonempty draw accept between
    (fun _ _ _ => b) b nonnegative (fun _ _ _ _ _ _ => le_rfl) h
  exact bound.trans (add_le_add_left constant _)
end Generic

open AspisV5ComponentCQM31TowerExact AspisV8.SecureCircleParameterDomain
variable {O H : Type*}

theorem actual_root_domination (coins : Finset O)
    (draw : H → O → Option (QM31Exact × H)) (between : QM31Exact → H → H)
    (S : Finset QM31Exact) (reward : QM31Exact → QM31Exact → H → ℚ)
    (bounded : ∀ first second next, Admissible first → Admissible second → second ≠ first →
      reward first second next ≤ if (first, second) ∈ S.offDiag then 1 else 0) (h : H) :
    Generic.pairPay coins draw Admissible between reward h ≤
      RootSetPairMass.targetMass coins draw between S h :=
  Generic.pairPay_root_domination coins draw Admissible between S reward bounded h

theorem actual_exception_bound (coins : Finset O) (nonempty : coins.Nonempty)
    (draw : H → O → Option (QM31Exact × H)) (between : QM31Exact → H → H)
    (S : Finset QM31Exact) (reward : QM31Exact → QM31Exact → H → ℚ)
    (b : ℚ) (nonnegative : 0 ≤ b)
    (bounded : ∀ first second next, Admissible first → Admissible second → second ≠ first →
      reward first second next ≤ (if (first, second) ∈ S.offDiag then 1 else 0) + b) (h : H) :
    Generic.pairPay coins draw Admissible between reward h ≤
      RootSetPairMass.targetMass coins draw between S h + b :=
  Generic.pairPay_exception_bound coins nonempty draw Admissible between S reward b
    nonnegative bounded h

#print axioms Generic.pay_mono
#print axioms Generic.pairPay_mono
#print axioms Generic.pairPay_le_constant
#print axioms Generic.pairPay_indicator
#print axioms Generic.pairPay_root_domination
#print axioms Generic.pairPay_exception_bound
#print axioms actual_root_domination
#print axioms actual_exception_bound
end
end AspisV8.NestedCircleContinuation
