import OrderedQueryGame
import PostQueryFunctional

/-! A constructed ordered game from the natural-line research functional.
No same_prior, zero_iff, degree, or relation-tail equality is supplied by the
caller. The remaining anchor-to-received support hypothesis is explicit.
This is a field-level constructor, not a translated byte-verifier theorem. -/
set_option autoImplicit false
namespace AspisV8.OrderedPostQueryGame
open Finset Polynomial
open AspisV8.JointImageGame AspisV8.OptimizedRelationRefinement
open AspisV8.PostQueryFunctional
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]

noncomputable def fromPrefix {D B : Finset K} {q : ℕ}
    (p : Prefix (K := K)) (hq : p.quarter*4=1) (final : Fin 256 → K)
    (received : K → K)
    (agrees : ∀ x ∈ D, x ∉ B → received x = lineEval p.referenceFinal x)
    (raw : OrderedQueryGame.Schedule D q → K → RawRounds (K := K) 3 256) :
    OrderedQueryGame.After D B q 255 p.trueError where
  difference := p.difference final
  degree := difference_degree p final
  noise := noise p received
  noise_zero := by
    intro x hx hB
    exact sub_eq_zero.mpr (agrees x hx hB)
  prior := p.prior final
  same_prior := same_prior p final
  residual := fun s => residual final (fun j => (s j : K)) received
  zero_iff := fun s => residual_zero_iff p final (fun j => (s j : K)) received
  tail := fun s rho => tail p hq final (fun j => (s j : K)) received rho (raw s rho)

theorem actual_tail_acceptance_iff {D B : Finset K} {q : ℕ}
    (p : Prefix (K := K)) (hq : p.quarter*4=1) (final : Fin 256 → K)
    (received : K → K)
    (agrees : ∀ x ∈ D, x ∉ B → received x = lineEval p.referenceFinal x)
    (raw : OrderedQueryGame.Schedule D q → K → RawRounds (K := K) 3 256)
    (s : OrderedQueryGame.Schedule D q) (rho : K) (alphas : List K) :
    (raw s rho).accepts p.quarter (postWeights p (fun j => (s j : K)) rho)
      final (postClaim p (fun j => (s j : K)) received rho) alphas ↔
      terminalZero ((fromPrefix p hq final received agrees raw).tail s rho) alphas :=
  tail_acceptance_iff p hq final (fun j => (s j : K)) received rho (raw s rho) alphas

/-- The false incoming discrepancy is the one computed from the actual
compact response and reference convolution, not a supplied scalar repair model. -/
theorem wrong_reference_bound {D B : Finset K} {q : ℕ}
    (p : Prefix (K := K)) (hq : p.quarter*4=1) (final : Fin 256 → K)
    (received : K → K)
    (agrees : ∀ x ∈ D, x ∉ B → received x = lineEval p.referenceFinal x)
    (raw : OrderedQueryGame.Schedule D q → K → RawRounds (K := K) 3 256)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0 < q) (hcount : q ≤ D.card) (wrong : p.trueError ≠ 0) :
    (fromPrefix p hq final received agrees raw).prob A G ≤
      ((B.card+255).choose q : ℚ)/D.card.choose q + (q:ℚ)/G.card + 18/A.card :=
  OrderedQueryGame.after_false_bound (fromPrefix p hq final received agrees raw)
    A G ha hg hpos hcount wrong

/-- A different adaptive final is bounded even if the reference discrepancy
is zero. Final is fixed before the fresh ordered schedule; raw may depend on
that full schedule and rho, then on each later relation challenge. -/
theorem different_final_bound {D B : Finset K} {q : ℕ}
    (p : Prefix (K := K)) (hq : p.quarter*4=1) (final : Fin 256 → K)
    (received : K → K)
    (agrees : ∀ x ∈ D, x ∉ B → received x = lineEval p.referenceFinal x)
    (raw : OrderedQueryGame.Schedule D q → K → RawRounds (K := K) 3 256)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0 < q) (hcount : q ≤ D.card) (different : final ≠ p.referenceFinal) :
    (fromPrefix p hq final received agrees raw).prob A G ≤
      ((B.card+255).choose q : ℚ)/D.card.choose q + (q:ℚ)/G.card + 18/A.card := by
  have hdiff : p.difference final ≠ 0 :=
    fun zero => different ((difference_zero_iff p final).mp zero)
  apply OrderedQueryGame.after_off_final_bound
    (fromPrefix p hq final received agrees raw) A G ha hg hpos hcount
  dsimp only [fromPrefix]
  exact hdiff

#print axioms fromPrefix
#print axioms actual_tail_acceptance_iff
#print axioms wrong_reference_bound
#print axioms different_final_bound
end AspisV8.OrderedPostQueryGame
