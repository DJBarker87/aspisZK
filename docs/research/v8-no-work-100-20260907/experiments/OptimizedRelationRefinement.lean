import AspisFormal.V6RelationFold
import AspisFormal.V6TranscriptRelationGrammar
import JointImageGame

/-! Research source-shaped refinement of the compact relation grammar.
The prover supplies six arbitrary fields, not an asserted discrepancy polynomial.
The missing quartic, honest convolution, degree, boundary and next discrepancy
are constructed using the exact generic algebra already consumed by V7.
No code membership, recovery, witness validity or fresh-challenge law is assumed.
This is not an Aeneas translation of the Rust structured-weight evaluator. -/
set_option autoImplicit false
namespace AspisV8.OptimizedRelationRefinement
open Polynomial
open AspisV5RelationSumcheckSoundness AspisV5FriRelationCandidateBridge
open AspisV5ComponentCRelationRowLinearity AspisV5ComponentCConcreteFoldLinearity
open AspisV6TranscriptRelationGrammar AspisV8.JointImageGame
universe u
variable {K : Type u} [Field K] [DecidableEq K]

abbrev Sent (K : Type*) := RelationRoundParts K

theorem inverse_quarter_exact (hfour : (4 : K) ≠ 0) : (4 : K)⁻¹*4=1 :=
  inv_mul_cancel₀ hfour

noncomputable def claimed (quarter claim : K) (sent : Sent K) : K[X] :=
  relationPolynomial (relationCoefficient quarter claim sent)

def nextClaim (quarter claim : K) (sent : Sent K) (a : K) : K :=
  relationEvaluate quarter claim sent a

/-- The source's reversed-coefficient Horner loop, written without the loop. -/
def sourceHorner (quarter claim : K) (sent : Sent K) (a : K) : K :=
  sent.c0 + a*(sent.c1 + a*(sent.c2 + a*(sent.c3 +
    a*((claim*quarter-sent.c0) + a*(sent.c5+a*sent.c6)))))

theorem nextClaim_source_horner (quarter claim : K) (sent : Sent K) (a : K) :
    nextClaim quarter claim sent a = sourceHorner quarter claim sent a := by
  simp [nextClaim, relationEvaluate, relationCoefficient,
    reconstructedRelationQuartic, Fin.sum_univ_seven, sourceHorner]
  ring

theorem compact_sent_not_omitted (quarter claim : K) (sent : Sent K) (j : Fin 6) :
    relationCoefficient quarter claim sent (![0,1,2,3,5,6] j) = sent.sent j := by
  fin_cases j <;> rfl

theorem claimed_eval (quarter claim : K) (sent : Sent K) (a : K) :
    (claimed quarter claim sent).eval a = nextClaim quarter claim sent a := by
  exact eval_relationPolynomial _ _

theorem boundary_represented (coeff : Fin 7 → K) :
    boundary (relationPolynomial coeff) = relationBoundary coeff := by
  simp only [boundary, relationBoundary,
    show (0 : ℕ) = (0 : Fin 7).val from rfl,
    show (4 : ℕ) = (4 : Fin 7).val from rfl, coeff_relationPolynomial]

theorem claimed_boundary (quarter claim : K) (sent : Sent K)
    (hq : quarter * 4 = 1) : boundary (claimed quarter claim sent) = claim := by
  rw [claimed, boundary_represented]
  have h := reconstructed_relation_quartic_has_exact_boundary quarter claim sent hq
  simpa [relationBoundary, relationCoefficient, relationBoundaryFromParts, mul_comm] using h

noncomputable def discrepancy (n : Nat) (quarter claim : K) (sent : Sent K)
    (weights values : Fin (4*n) → K) : K[X] :=
  claimed quarter claim sent - relationPolynomial (polynomialForExtension n weights values)

theorem discrepancy_degree (n : Nat) (quarter claim : K) (sent : Sent K)
    (weights values : Fin (4*n) → K) :
    (discrepancy n quarter claim sent weights values).natDegree ≤ 6 :=
  natDegree_relationPolynomial_sub_le_six _ _

theorem discrepancy_boundary (n : Nat) (quarter claim : K) (sent : Sent K)
    (weights values : Fin (4*n) → K) (hq : quarter * 4 = 1) :
    boundary (discrepancy n quarter claim sent weights values) =
      claim - candidateClaim weights values := by
  have hfour : (4 : K) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hq
    exact zero_ne_one hq
  have hlinear (p q : K[X]) : boundary (p-q) = boundary p - boundary q := by
    simp only [boundary, Polynomial.coeff_sub]
    ring
  rw [discrepancy, hlinear, claimed_boundary _ _ _ hq, boundary_represented,
    relationBoundary_polynomialForExtension n weights values hfour]
  rfl

theorem discrepancy_eval (n : Nat) (quarter claim : K) (sent : Sent K)
    (weights values : Fin (4*n) → K) (a : K) :
    (discrepancy n quarter claim sent weights values).eval a =
      nextClaim quarter claim sent a - candidateClaim
        (dualWeightFoldLayer n a weights) (coefficientFoldLayer n a values) := by
  rw [discrepancy, Polynomial.eval_sub, claimed_eval,
    relationPolynomial_polynomialForExtension_eval]
  rfl

/-- This constructor has only six arbitrary response fields and a causal
continuation. It derives, rather than requests, the Rounds boundary/evaluation
interfaces. `next` may depend on this round's revealed challenge. -/
noncomputable def compactStep {r n : Nat} (quarter claim : K) (sent : Sent K)
    (weights values : Fin (4*n) → K) (hq : quarter * 4 = 1)
    (next : (a : K) → Rounds r (nextClaim quarter claim sent a - candidateClaim
      (dualWeightFoldLayer n a weights) (coefficientFoldLayer n a values))) :
    Rounds (r+1) (claim - candidateClaim weights values) :=
  Rounds.step (discrepancy n quarter claim sent weights values)
    (discrepancy_degree n quarter claim sent weights values)
    (discrepancy_boundary n quarter claim sent weights values hq)
    (fun a => (discrepancy_eval n quarter claim sent weights values a).symm ▸ next a)

/-- A raw relation suffix, before assigning it any discrepancy invariant.
Length zero is the actual scalar-to-dot equality; each response is fixed before
its own challenge. Instantiations are 3 rounds on 256, or 4 on 1024. -/
inductive RawRounds : Nat → Nat → Type u
  | done (n : Nat) : RawRounds 0 n
  | step {r n : Nat} (sent : Sent K) (next : K → RawRounds r n) : RawRounds (r+1) (4*n)

noncomputable def RawRounds.toGame (quarter : K) (hq : quarter*4=1) :
    {r n : Nat} → RawRounds (K := K) r n → (weights values : Fin n → K) →
      (claim : K) → Rounds r (claim-candidateClaim weights values)
  | _, _, .done _, weights, values, claim => .done (claim-candidateClaim weights values)
  | _, _, .step sent next, weights, values, claim =>
      compactStep quarter claim sent weights values hq (fun a =>
        (next a).toGame quarter hq
          (dualWeightFoldLayer _ a weights) (coefficientFoldLayer _ a values)
          (nextClaim quarter claim sent a))

/-- Actual field-level execution of the compact suffix. Wrong challenge-list
length fails closed; no terminal success field is supplied by the strategy. -/
def RawRounds.accepts (quarter : K) : {r n : Nat} → RawRounds (K := K) r n →
    (weights values : Fin n → K) → K → List K → Prop
  | _, _, .done _, weights, values, claim, [] => candidateClaim weights values=claim
  | _, _, .step sent next, weights, values, claim, a::as =>
      (next a).accepts quarter (dualWeightFoldLayer _ a weights)
        (coefficientFoldLayer _ a values) (nextClaim quarter claim sent a) as
  | _, _, _, _, _, _, _ => False

def terminalZero : {r : Nat} → {c : K} → Rounds r c → List K → Prop
  | _, c, .done _, [] => c=0
  | _, _, .step _ _ _ next, a::as => terminalZero (next a) as
  | _, _, _, _ => False

@[simp] theorem terminalZero_transport {r : Nat} {c d : K} (h : c=d)
    (g : Rounds r c) (alphas : List K) :
    terminalZero (h ▸ g) alphas ↔ terminalZero g alphas := by
  cases h
  rfl

theorem raw_acceptance_iff_terminal_zero (quarter : K) (hq : quarter*4=1)
    {r n : Nat} (raw : RawRounds (K := K) r n) (weights values : Fin n → K)
    (claim : K) (alphas : List K) :
    raw.accepts quarter weights values claim alphas ↔
      terminalZero (raw.toGame quarter hq weights values claim) alphas := by
  induction raw generalizing claim alphas with
  | done n =>
      cases alphas <;> simp [RawRounds.accepts, RawRounds.toGame, terminalZero,
        sub_eq_zero, eq_comm]
  | @step r n sent next ih =>
      cases alphas with
      | nil => simp [RawRounds.accepts, RawRounds.toGame, compactStep, terminalZero]
      | cons a as =>
          simpa [RawRounds.accepts, RawRounds.toGame, compactStep, terminalZero]
            using ih a (dualWeightFoldLayer n a weights) (coefficientFoldLayer n a values)
              (nextClaim quarter claim sent a) as

/-- Reuse (not re-prove) the existing sequential-repair bound for the newly
constructed actual compact suffix. The wrong incoming dot is explicit; this
does not assert that every accepting prefix has such a discrepancy. -/
theorem compact_tail_wrong_bound (quarter : K) (hq : quarter*4=1)
    (raw : RawRounds (K := K) 3 256) (weights final : Fin 256 → K)
    (claim : K) (A : Finset K) (ha : A.Nonempty)
    (hwrong : claim ≠ candidateClaim weights final) :
    (raw.toGame quarter hq weights final claim).prob A ≤ 18 / (A.card : ℚ) := by
  have h := rounds_false_bound A ha (raw.toGame quarter hq weights final claim)
    (sub_ne_zero.mpr hwrong)
  norm_num at h ⊢
  exact h

#print axioms claimed_eval
#print axioms inverse_quarter_exact
#print axioms nextClaim_source_horner
#print axioms compact_sent_not_omitted
#print axioms claimed_boundary
#print axioms discrepancy_degree
#print axioms discrepancy_boundary
#print axioms discrepancy_eval
#print axioms compactStep
#print axioms RawRounds.toGame
#print axioms raw_acceptance_iff_terminal_zero
#print axioms compact_tail_wrong_bound
end AspisV8.OptimizedRelationRefinement
