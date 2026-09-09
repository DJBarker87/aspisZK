import FirstImageDiscrepancy
import OrderedPostQueryGame

/-! A pre-tau strategy and fixed four-slot oracle, followed by the real compact
field grammar. The received slots are not assumed globally polynomial. The
explicit anchor support remains a coverage hypothesis, never an acceptance
consequence. Source parsing/authentication and the FS lift are separate. -/
set_option autoImplicit false
namespace AspisV8.CausalOrderedRelation
open Polynomial Finset
open AspisV8.JointImageGame AspisV8.OptimizedRelationRefinement
open AspisV8.PostQueryFunctional AspisV8.FirstImageDiscrepancy
open AspisV5FriConcreteEncoderCommutation AspisV5ComponentCConcreteFoldLinearity
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]

/-- The received value and interpolant are actual field inputs. This is the
V8 quotient/reconstruction equality, not V7 raw-word consistency substituted
for it. Zero denominators remain excluded, as on the checked source path. -/
theorem quotient_eq_iff_reconstructed (received interpolant denominator value : K)
    (nonzero : denominator ≠ 0) :
    (received-interpolant)/denominator=value ↔
      received=denominator*value+interpolant := by
  rw [div_eq_iff nonzero]
  constructor <;> intro h <;> linear_combination h

/-- Data and the quotient anchor are fixed BEFORE tau. Coordinates encode the
four-slot fibre over its final-domain point. Outside B the whole received
fibre agrees with Q; inside B all four slots are arbitrary. -/
structure FixedOracle (D B : Finset K) (Q : Fin 1024 → K) where
  x : K → K
  y : K → K
  slots : K → Fin 4 → K
  x_nonzero : ∀ t ∈ D, x t ≠ 0
  y_nonzero : ∀ t ∈ D, y t ≠ 0
  coordinate : ∀ t ∈ D, 2*(x t)^2-1 = t
  supported : ∀ t ∈ D, t ∉ B → slots t = circleFibre Q (x t) (y t)

/-- A causal batched received word can be non-polynomial. This constructor
derives its virtual quotient support from agreement with L*Q+I on that
same supplied support; it does not infer original component membership. -/
noncomputable def fromReconstruction {D B : Finset K} (Q : Fin 1024 → K)
    (x y : K → K) (received interpolant denominator : K → Fin 4 → K)
    (hx : ∀ t ∈ D, x t ≠ 0) (hy : ∀ t ∈ D, y t ≠ 0)
    (coordinate : ∀ t ∈ D, 2*(x t)^2-1=t)
    (hd : ∀ t ∈ D, ∀ j, denominator t j ≠ 0)
    (agreement : ∀ t ∈ D, t ∉ B → ∀ j,
      received t j=denominator t j*circleFibre Q (x t) (y t) j+interpolant t j) :
    FixedOracle D B Q where
  x := x
  y := y
  slots := fun t j => (received t j-interpolant t j)/denominator t j
  x_nonzero := hx
  y_nonzero := hy
  coordinate := coordinate
  supported := by
    intro t ht hb
    funext j
    exact (quotient_eq_iff_reconstructed _ _ _ _ (hd t ht j)).mpr (agreement t ht hb j)

noncomputable def FixedOracle.folded {D B : Finset K} {Q : Fin 1024 → K}
    (o : FixedOracle D B Q) (alpha : K) (t : K) : K :=
  circleFoldValue alpha (2*o.x t)⁻¹ (2*o.y t)⁻¹ (o.slots t)

theorem FixedOracle.folded_support {D B : Finset K} {Q : Fin 1024 → K}
    (o : FixedOracle D B Q) (alpha : K) :
    ∀ t ∈ D, t ∉ B → o.folded alpha t =
      lineEval (coefficientFoldLayer 256 alpha Q) t := by
  intro t ht hb
  unfold FixedOracle.folded
  rw [o.supported t ht hb,
    circleFibre_fold Q alpha (o.x t) (o.y t) (o.x_nonzero t ht) (o.y_nonzero t ht),
    o.coordinate t ht]

/-- response0 knows tau, but not alpha0. The final knows both, not future
queries. The raw tail knows ordered queries and rho; its inductive type only
reveals subsequent alpha challenges after each compact response. -/
structure Strategy (D : Finset K) (q : ℕ) where
  firstResponse : K → Sent K
  final : K → K → Fin 256 → K
  rawTail : K → K → OrderedQueryGame.Schedule D q → K → RawRounds (K := K) 3 256

def atFold {D : Finset K} {q : ℕ} (pre : Before (K := K))
    (s : Strategy D q) (tau alpha : K) : Prefix (K := K) :=
  pre.snapshot tau (s.firstResponse tau) alpha

theorem prefix_support {D B : Finset K} {q : ℕ} (pre : Before (K := K))
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q) (tau alpha : K) :
    ∀ t ∈ D, t ∉ B → o.folded alpha t =
      lineEval (atFold pre s tau alpha).referenceFinal t :=
  o.folded_support alpha

noncomputable def after {D B : Finset K} {q : ℕ} (pre : Before (K := K))
    (hq : pre.quarter*4=1) (o : FixedOracle D B pre.referenceQ)
    (s : Strategy D q) (tau alpha : K) :
    OrderedQueryGame.After D B q 255 ((pre.firstError tau (s.firstResponse tau)).eval alpha) :=
  OrderedPostQueryGame.fromPrefix (atFold pre s tau alpha) hq (s.final tau alpha)
    (o.folded alpha) (prefix_support pre o s tau alpha) (s.rawTail tau alpha)

noncomputable def probability {D B : Finset K} {q : ℕ} (pre : Before (K := K))
    (hq : pre.quarter*4=1) (o : FixedOracle D B pre.referenceQ)
    (s : Strategy D q) (A G : Finset K) : ℚ :=
  avg G (fun tau => avg A (fun alpha => (after pre hq o s tau alpha).prob A G))

/-- This checks the actual compact tail, not a Boolean acceptance supplied
by a strategy. Incompatible challenge-list lengths are rejected by RawRounds. -/
def accepts {D B : Finset K} {q : ℕ} (pre : Before (K := K))
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (tau alpha : K) (queries : OrderedQueryGame.Schedule D q) (rho : K)
    (later : List K) : Prop :=
  (s.rawTail tau alpha queries rho).accepts pre.quarter
    (postWeights (atFold pre s tau alpha) (fun j => (queries j : K)) rho)
    (s.final tau alpha)
    (postClaim (atFold pre s tau alpha) (fun j => (queries j : K)) (o.folded alpha) rho) later

theorem acceptance_iff_terminal_zero {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (tau alpha : K) (queries : OrderedQueryGame.Schedule D q) (rho : K) (later : List K) :
    accepts pre o s tau alpha queries rho later ↔
      terminalZero ((after pre hq o s tau alpha).tail queries rho) later :=
  OrderedPostQueryGame.actual_tail_acceptance_iff (atFold pre s tau alpha) hq
    (s.final tau alpha) (o.folded alpha) (prefix_support pre o s tau alpha)
    (s.rawTail tau alpha) queries rho later

theorem after_unit {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (tau alpha : K) (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hcount : q ≤ D.card) : (after pre hq o s tau alpha).prob A G ≤ 1 := by
  apply avg_le _ (OrderedQueryGame.schedules_nonempty D q hcount) _ _
  intro queries _
  apply avg_le G hg
  intro rho _
  exact (rounds_unit A ha ((after pre hq o s tau alpha).tail queries rho)).2

theorem probability_unit {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (hcount : q ≤ D.card) :
    probability pre hq o s A G ≤ 1 :=
  avg_le G hg _ _ (fun tau _ =>
    avg_le A ha _ _ (fun alpha _ => after_unit pre hq o s tau alpha A G ha hg hcount))

theorem first_stage_bound {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (tau : K) (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0 < q) (hcount : q ≤ D.card)
    (wrong : pre.errorPolynomial.eval tau ≠ 0) :
    avg A (fun alpha => (after pre hq o s tau alpha).prob A G) ≤
      6/A.card + (((B.card+255).choose q : ℚ)/D.card.choose q + (q:ℚ)/G.card + 18/A.card) := by
  apply avg_polynomial A ha (pre.firstError tau (s.firstResponse tau))
    (firstError_nonzero pre hq tau (s.firstResponse tau) wrong) 6
    (firstError_degree pre tau (s.firstResponse tau)) _ _ (by positivity)
    (fun alpha _ => after_unit pre hq o s tau alpha A G ha hg hcount)
  intro alpha _ nonzero
  exact OrderedQueryGame.after_false_bound (after pre hq o s tau alpha)
    A G ha hg hpos hcount nonzero

/-- Reuses the existing root/repair bounds with DERIVED image and first-round
polynomials. All four relation repairs are charged once. No first response
can be selected after alpha0 in Strategy. -/
theorem bad_anchor_bound {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0 < q) (hcount : q ≤ D.card)
    (bad : pre.prior ≠ 0 ∨ pre.E1 ≠ 0 ∨ pre.E2 ≠ 0) :
    probability pre hq o s A G ≤
      ((q:ℚ)+2)/G.card + 24/A.card + ((B.card+255).choose q : ℚ)/D.card.choose q := by
  have h := avg_polynomial G hg pre.errorPolynomial
    (AspisV8.RobustImageGame.image_nonzero_any pre.prior pre.E1 pre.E2 bad) 2
    (error_degree pre)
    (fun tau => avg A (fun alpha => (after pre hq o s tau alpha).prob A G))
    (6/A.card + (((B.card+255).choose q : ℚ)/D.card.choose q + (q:ℚ)/G.card + 18/A.card))
    (by positivity)
    (fun tau _ => avg_le A ha _ _ (fun alpha _ => after_unit pre hq o s tau alpha A G ha hg hcount))
    (fun tau _ hn => first_stage_bound pre hq o s tau A G ha hg hpos hcount hn)
  change avg _ _ ≤ _
  convert h using 1 <;> ring

/-- An image-valid reference with a wrong ordinary relation needs no tau
cancellation charge: its actual incoming discrepancy is constant in tau.
This is the interface used by the shifted ordinary-row composition. -/
theorem image_valid_wrong_bound {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0 < q) (hcount : q ≤ D.card)
    (h1 : pre.E1=0) (h2 : pre.E2=0) (wrong : pre.prior ≠ 0) :
    probability pre hq o s A G ≤
      (q:ℚ)/G.card + 24/A.card + ((B.card+255).choose q : ℚ)/D.card.choose q := by
  have h := avg_le G hg
    (fun tau => avg A (fun alpha => (after pre hq o s tau alpha).prob A G))
    (6/A.card+(((B.card+255).choose q : ℚ)/D.card.choose q+(q:ℚ)/G.card+18/A.card))
    (fun tau _ => first_stage_bound pre hq o s tau A G ha hg hpos hcount (by
      simpa only [Before.errorPolynomial, imagePolynomial_eval, h1, h2,
        mul_zero, sub_zero] using wrong))
  change avg _ _ ≤ _
  convert h using 1 <;> ring

/-- Even when the fixed anchor is correct, accepted differing-final branches
are retained and charged, not discarded by a successful-candidate predicate. -/
noncomputable def differentFinalProbability {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q) (A G : Finset K) : ℚ := by
  classical
  exact avg G (fun tau => avg A (fun alpha =>
    if s.final tau alpha = (atFold pre s tau alpha).referenceFinal then 0
    else (after pre hq o s tau alpha).prob A G))

theorem different_final_bound {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0 < q) (hcount : q ≤ D.card) :
    differentFinalProbability pre hq o s A G ≤
      ((B.card+255).choose q : ℚ)/D.card.choose q + (q:ℚ)/G.card + 18/A.card := by
  classical
  apply avg_le G hg
  intro tau _
  apply avg_le A ha
  intro alpha _
  split
  · positivity
  · rename_i different
    exact OrderedPostQueryGame.different_final_bound (atFold pre s tau alpha) hq
      (s.final tau alpha) (o.folded alpha) (prefix_support pre o s tau alpha)
      (s.rawTail tau alpha) A G ha hg hpos hcount different

#print axioms FixedOracle.folded_support
#print axioms quotient_eq_iff_reconstructed
#print axioms fromReconstruction
#print axioms after
#print axioms acceptance_iff_terminal_zero
#print axioms probability_unit
#print axioms first_stage_bound
#print axioms bad_anchor_bound
#print axioms image_valid_wrong_bound
#print axioms different_final_bound
end AspisV8.CausalOrderedRelation
