import ChordRationalBadOOD
import CausalOrderedRelation

/-! A causal ideal-game bound for a POLYNOMIAL raw message U with a wrong
batched OOD answer. U and all OOD data are fixed before tau and alpha0.
The virtual quotient is rational, not assumed polynomial. At norm poles the
game permits arbitrary values; they remain inside the 259-point exceptional
matching set. Ordered radial queries inject their actual line coordinates
2*s-1 into the existing compact relation grammar. No Rust parser or global
authentication refinement is claimed here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.ChordRationalQueryGame
noncomputable section
open Polynomial Finset
open AspisV5FriConcreteEncoderApplicability AspisV5FriConcreteEncoderCommutation
open AspisV8.ChordRationalAlgebra AspisV8.ChordRationalDegree
open AspisV8.ChordRationalOOD AspisV8.ChordRationalBadOOD
open AspisV8.OODInterpolant AspisV8.ComponentOODBinding
open AspisV8.JointImageGame AspisV8.PostQueryFunctional
open AspisV8.OptimizedRelationRefinement AspisV8.FirstImageDiscrepancy
open AspisV8.CausalOrderedRelation
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]

def radialFinal (final : Fin 256 → K) : K[X] :=
  (naturalCoefficientPolynomial final).comp (C 2*X-1)

theorem affine_comp_degree (p : K[X]) (d : Nat) (hp : p.natDegree≤d) :
    (p.comp (C 2*X-1)).natDegree≤d := by
  have ha : (C (2:K)*X-1).natDegree≤1 := by compute_degree
  calc
    (p.comp (C 2*X-1)).natDegree≤p.natDegree*(C 2*X-1).natDegree := natDegree_comp_le
    _ ≤ d*1 := Nat.mul_le_mul hp ha
    _ = d := Nat.mul_one d

theorem radial_final_degree (final : Fin 256 → K) :
    (radialFinal final).natDegree≤255 :=
  affine_comp_degree _ _ (naturalCoefficientPolynomial_natDegree_le (by decide) final)

theorem radial_lanes_degree (U : Fin 1024 → K) :
    ∀ j, (radialLanes U j).natDegree≤255 := by
  intro j
  exact affine_comp_degree _ _
    (naturalCoefficientPolynomial_natDegree_le (by decide) (coefficientLane 256 j U))

theorem radial_final_eval (final : Fin 256 → K) (s : K) :
    (radialFinal final).eval s=lineEval final (finalFromRadial s) := by
  simp only [radialFinal,eval_comp,eval_sub,eval_mul,eval_C,eval_X,eval_one,
    lineEval,finalFromRadial]

/-- Arbitrary pole values are a conservative overapproximation, not hints
accepted by the source. They may depend on tau/alpha, but not future queries. -/
def received (d : Data (K:=K)) (U : Fin 1024 → K)
    (pole : K → K → K → K) (tau alpha z : K) : K :=
  let s := radialFromFinal z
  if (clearedNorm d.a d.b d.c).eval s=0 then pole tau alpha z
  else rationalFold d.a d.b d.c alpha (radialLanes (U-d.interpolant)) s

def points {D : Finset K} {q : Nat} (queries : OrderedQueryGame.Schedule D q) : Fin q → K :=
  fun j=>finalFromRadial (queries j : K)

def residuals {D : Finset K} {q : Nat} (d : Data (K:=K)) (U : Fin 1024 → K)
    (pole : K → K → K → K) (strategy : Strategy D q) (tau alpha : K)
    (queries : OrderedQueryGame.Schedule D q) : Fin q → K :=
  residual (strategy.final tau alpha) (points queries) (received d U pole tau alpha)

def matches {D : Finset K} {q : Nat} (d : Data (K:=K)) (U : Fin 1024 → K)
    (strategy : Strategy D q) (tau alpha : K) (s : K) : Prop :=
  (clearedNorm d.a d.b d.c).eval s=0 ∨
    rationalFold d.a d.b d.c alpha (radialLanes (U-d.interpolant)) s=
      (radialFinal (strategy.final tau alpha)).eval s

theorem zero_residual_matches {D : Finset K} {q : Nat}
    (d : Data (K:=K)) (U : Fin 1024 → K) (pole : K → K → K → K)
    (strategy : Strategy D q) (tau alpha : K) (queries : OrderedQueryGame.Schedule D q)
    (zero : residuals d U pole strategy tau alpha queries=0) :
    ∀ j, matches d U strategy tau alpha (queries j : K) := by
  intro j
  by_cases hp : (clearedNorm d.a d.b d.c).eval (queries j : K)=0
  · exact Or.inl hp
  · apply Or.inr
    have hz := congrFun zero j
    simp only [residuals,residual,points,received,
      radial_from_final_inverse (NeZero.ne (2:K)),hp,if_false,Pi.zero_apply] at hz
    exact (sub_eq_zero.mp hz).symm.trans (radial_final_eval _ _).symm

/-- Uses the actual first response, folded ordinary/image weights, shifted
query scalar, and three sequential compact responses. No free error equality
or Boolean acceptance predicate is supplied to this constructor. -/
def tailGame {D : Finset K} {q : Nat} (pre : Before (K:=K)) (quarter : pre.quarter*4=1)
    (d : Data (K:=K)) (U : Fin 1024 → K) (pole : K → K → K → K)
    (strategy : Strategy D q) (tau alpha : K) (queries : OrderedQueryGame.Schedule D q)
    (rho : K) :
    Rounds 3 ((shifted ((atFold pre strategy tau alpha).prior (strategy.final tau alpha))
      (residuals d U pole strategy tau alpha queries)).eval rho) :=
  PostQueryFunctional.tail (atFold pre strategy tau alpha) quarter
    (strategy.final tau alpha) (points queries) (received d U pole tau alpha) rho
    (strategy.rawTail tau alpha queries rho)

def suffixProbability {D : Finset K} {q : Nat}
    (pre : Before (K:=K)) (quarter : pre.quarter*4=1)
    (d : Data (K:=K)) (U : Fin 1024 → K) (pole : K → K → K → K)
    (strategy : Strategy D q) (tau alpha : K) (A G : Finset K) : ℚ :=
  avg univ (fun queries=>avg G (fun rho=>
    (tailGame pre quarter d U pole strategy tau alpha queries rho).prob A))

def probability {D : Finset K} {q : Nat}
    (pre : Before (K:=K)) (quarter : pre.quarter*4=1)
    (d : Data (K:=K)) (U : Fin 1024 → K) (pole : K → K → K → K)
    (strategy : Strategy D q) (A G : Finset K) : ℚ :=
  avg G (fun tau=>avg A (fun alpha=>
    suffixProbability pre quarter d U pole strategy tau alpha A G))

theorem actual_acceptance_iff {D : Finset K} {q : Nat}
    (pre : Before (K:=K)) (quarter : pre.quarter*4=1)
    (d : Data (K:=K)) (U : Fin 1024 → K) (pole : K → K → K → K)
    (strategy : Strategy D q) (tau alpha : K) (queries : OrderedQueryGame.Schedule D q)
    (rho : K) (later : List K) :
    (strategy.rawTail tau alpha queries rho).accepts pre.quarter
      (postWeights (atFold pre strategy tau alpha) (points queries) rho)
      (strategy.final tau alpha)
      (postClaim (atFold pre strategy tau alpha) (points queries) (received d U pole tau alpha) rho)
      later ↔ terminalZero (tailGame pre quarter d U pole strategy tau alpha queries rho) later :=
  tail_acceptance_iff (atFold pre strategy tau alpha) quarter
    (strategy.final tau alpha) (points queries) (received d U pole tau alpha) rho
    (strategy.rawTail tau alpha queries rho) later

theorem suffix_unit {D : Finset K} {q : Nat}
    (pre : Before (K:=K)) (quarter : pre.quarter*4=1)
    (d : Data (K:=K)) (U : Fin 1024 → K) (pole : K → K → K → K)
    (strategy : Strategy D q) (tau alpha : K) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hcount : q≤D.card) :
    suffixProbability pre quarter d U pole strategy tau alpha A G≤1 :=
  avg_le _ (OrderedQueryGame.schedules_nonempty D q hcount) _ _ (fun queries _=>
    avg_le _ hg _ _ (fun rho _=>
      (rounds_unit A ha (tailGame pre quarter d U pole strategy tau alpha queries rho)).2))

theorem different_suffix_bound {D : Finset K} {q : Nat}
    (pre : Before (K:=K)) (quarter : pre.quarter*4=1)
    (d : Data (K:=K)) (U : Fin 1024 → K) (pole : K → K → K → K)
    (strategy : Strategy D q) (tau alpha : K) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hpos : 0<q) (hcount : q≤D.card)
    (normNonzero : clearedNorm d.a d.b d.c≠0)
    (different : clearedDiscrepancy d.a d.b d.c alpha
      (radialLanes (U-d.interpolant)) (radialFinal (strategy.final tau alpha))≠0) :
    suffixProbability pre quarter d U pole strategy tau alpha A G≤
      ((259:Nat).choose q : ℚ)/D.card.choose q+(q:ℚ)/G.card+18/A.card := by
  classical
  let E := OrderedQueryGame.matching D q (matches d U strategy tau alpha)
  let eps : ℚ := (q:ℚ)/G.card+18/A.card
  have nonzero_tail (queries : OrderedQueryGame.Schedule D q)
      (hne : residuals d U pole strategy tau alpha queries≠0) :
      avg G (fun rho=>(tailGame pre quarter d U pole strategy tau alpha queries rho).prob A)≤eps := by
    apply avg_polynomial G hg
      (shifted ((atFold pre strategy tau alpha).prior (strategy.final tau alpha))
        (residuals d U pole strategy tau alpha queries))
      (shifted_nonzero _ _ (Or.inr hne)) q (shifted_degree hpos _ _)
      _ (18/A.card) (by positivity)
      (fun rho _=>(rounds_unit A ha (tailGame pre quarter d U pole strategy tau alpha queries rho)).2)
    intro rho _ hn
    convert rounds_false_bound A ha
      (tailGame pre quarter d U pole strategy tau alpha queries rho) hn using 1 <;> norm_num
  have h := avg_exception univ E (OrderedQueryGame.schedules_nonempty D q hcount)
    (Finset.subset_univ _) _ eps (by dsimp [eps]; positivity)
    (fun queries _=>avg_le G hg _ _ (fun rho _=>
      (rounds_unit A ha (tailGame pre quarter d U pole strategy tau alpha queries rho)).2))
    (by
      intro queries _ outside
      apply nonzero_tail queries
      intro zero
      exact outside (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        zero_residual_matches d U pole strategy tau alpha queries zero⟩))
  have size : (D.filter (matches d U strategy tau alpha)).card≤259 :=
    degree255_possible_match_card_le D d.a d.b d.c alpha
      (radialLanes (U-d.interpolant)) (radialFinal (strategy.final tau alpha))
      (radial_lanes_degree _) (radial_final_degree _) normNonzero different
  have ratio : (E.card:ℚ)/Fintype.card (OrderedQueryGame.Schedule D q)≤
      ((259:Nat).choose q:ℚ)/D.card.choose q := by
    rw [OrderedQueryGame.ordered_matching_ratio]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.choose_le_choose q size
  rw [Finset.card_univ] at h
  change avg _ _≤_
  dsimp [eps] at h
  linarith

/-- Wrong BATCHED OOD claims for the fixed polynomial raw U. Finals are
adaptive in tau and alpha. The at-most-three exact continuations are charged,
not conditioned away; all other continuations use their actual query checks.
No first-round or image root term is needed because the suffix bound permits
an arbitrary prior discrepancy, including a maliciously repaired zero prior. -/
theorem wrong_batched_ood_bound {D : Finset K} {q : Nat}
    (pre : Before (K:=K)) (quarter : pre.quarter*4=1)
    (d : Data (K:=K)) (checked : d.Checked) (U : Fin 1024 → K)
    (pole : K → K → K → K) (strategy : Strategy D q) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hpos : 0<q) (hcount : q≤D.card)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (normNonzero : clearedNorm d.a d.b d.c≠0)
    (wrong : circleFunctional d.x0 d.y0 U≠d.batch 0 ∨
      circleFunctional d.x1 d.y1 U≠d.batch 1) :
    probability pre quarter d U pole strategy A G≤
      3/A.card+(q:ℚ)/G.card+18/A.card+((259:Nat).choose q:ℚ)/D.card.choose q := by
  classical
  apply avg_le G hg
  intro tau _
  let E := exactChallenges d U (fun alpha=>radialFinal (strategy.final tau alpha)) A
  have size : E.card≤3 := wrong_batched_ood_exact_challenges_le_three
    d checked U circles normNonzero wrong _ A
  let eps : ℚ := ((259:Nat).choose q:ℚ)/D.card.choose q+(q:ℚ)/G.card+18/A.card
  have h := avg_exception A E ha (Finset.filter_subset _ _) _ eps (by dsimp [eps]; positivity)
    (fun alpha _=>suffix_unit pre quarter d U pole strategy tau alpha A G ha hg hcount)
    (by
      intro alpha hα outside
      apply different_suffix_bound pre quarter d U pole strategy tau alpha A G
        ha hg hpos hcount normNonzero
      intro zero
      exact outside (Finset.mem_filter.mpr ⟨hα,zero⟩))
  have fraction : (E.card:ℚ)/A.card≤3/A.card :=
    div_le_div_of_nonneg_right (by exact_mod_cast size) (Nat.cast_nonneg _)
  dsimp [eps] at h
  linarith

theorem q22_full_field_bound [Fintype K] {D : Finset K}
    (domainCard : D.card=262144)
    (pre : Before (K:=K)) (quarter : pre.quarter*4=1)
    (d : Data (K:=K)) (checked : d.Checked) (U : Fin 1024 → K)
    (pole : K → K → K → K) (strategy : Strategy D 22)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (normNonzero : clearedNorm d.a d.b d.c≠0)
    (wrong : circleFunctional d.x0 d.y0 U≠d.batch 0 ∨
      circleFunctional d.x1 d.y1 U≠d.batch 1) :
    probability pre quarter d U pole strategy univ (univ.erase 0)≤
      3/(Fintype.card K:ℚ)+22/((Fintype.card K-1:Nat):ℚ)+
        18/(Fintype.card K:ℚ)+((259:Nat).choose 22:ℚ)/(262144:Nat).choose 22 := by
  have nonzeroSet : (univ.erase (0:K)).Nonempty := by
    exact ⟨1,Finset.mem_erase.mpr ⟨one_ne_zero,Finset.mem_univ _⟩⟩
  have hcount : 22≤D.card := by rw [domainCard]; decide
  have h := wrong_batched_ood_bound pre quarter d checked U pole strategy
    univ (univ.erase 0) Finset.univ_nonempty nonzeroSet (by decide) hcount circles normNonzero wrong
  simpa only [Finset.card_univ,Finset.card_erase_of_mem (Finset.mem_univ (0:K)),domainCard] using h

#print axioms radial_final_degree
#print axioms radial_lanes_degree
#print axioms zero_residual_matches
#print axioms tailGame
#print axioms actual_acceptance_iff
#print axioms different_suffix_bound
#print axioms wrong_batched_ood_bound
#print axioms q22_full_field_bound
end
end AspisV8.ChordRationalQueryGame
