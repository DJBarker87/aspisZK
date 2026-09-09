import CausalOrderedRelation

/-! Actual ordered compact suffix acceptance reduced to a relation-compatible
agreement moment. The received word is arbitrary; the final may be chosen
after alpha0, but is fixed before queries. No numeric bound on the moment,
anchor, decoded tuple, or polynomial received-word hypothesis is supplied.
The first response is causal in the final constructor below. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 400000
namespace AspisV8.RelationCompatibleMoment
open Finset Polynomial
open AspisV8.JointImageGame AspisV8.PostQueryFunctional
open AspisV8.OptimizedRelationRefinement AspisV8.CausalOrderedRelation
open AspisV8.FirstImageDiscrepancy AspisV8.OrderedQueryGame
open AspisV5FriRelationCandidateBridge
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

def matchingRatio (D : Finset K) (q : Nat) (final : Fin 256 → K)
    (received : K → K) : ℚ :=
  ((D.filter fun x => lineEval final x=received x).card.choose q : ℚ)/D.card.choose q

def compatibleMoment (p : Prefix (K := K)) (final : Fin 256 → K)
    (received : K → K) (D : Finset K) (q : Nat) : ℚ :=
  if p.prior final=0 then matchingRatio D q final received else 0

def suffixProbability {D : Finset K} {q : Nat}
    (p : Prefix (K := K)) (hq : p.quarter*4=1) (final : Fin 256 → K)
    (received : K → K) (raw : Schedule D q → K → RawRounds (K := K) 3 256)
    (A G : Finset K) : ℚ :=
  avg univ (fun s => avg G (fun rho =>
    (tail p hq final (fun j => (s j : K)) received rho (raw s rho)).prob A))

/-- No geometry enters this bound. A nonzero incoming discrepancy OR one
nonzero ordered query residual makes the actual shifted polynomial nonzero. -/
theorem schedule_false_bound {D : Finset K} {q : Nat}
    (p : Prefix (K := K)) (hq : p.quarter*4=1) (final : Fin 256 → K)
    (received : K → K) (raw : Schedule D q → K → RawRounds (K := K) 3 256)
    (s : Schedule D q) (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0<q)
    (wrong : p.prior final≠0 ∨ residual final (fun j => (s j : K)) received≠0) :
    avg G (fun rho =>
      (tail p hq final (fun j => (s j : K)) received rho (raw s rho)).prob A)≤
      (q:ℚ)/G.card+18/A.card := by
  apply avg_polynomial G hg
    (shifted (p.prior final) (residual final (fun j => (s j : K)) received))
    (shifted_nonzero _ _ wrong) q (shifted_degree hpos _ _) _ (18/A.card)
    (by positivity) (fun rho _ => (rounds_unit A ha _).2)
  intro rho _ nonzero
  convert rounds_false_bound A ha
    (tail p hq final (fun j => (s j : K)) received rho (raw s rho)) nonzero using 1 <;>
    norm_num

/-- The exact matching mass is retained ONLY when the actual prior is zero.
The scalar batch and three later degree-six repairs are charged once. -/
theorem suffix_bound {D : Finset K} {q : Nat}
    (p : Prefix (K := K)) (hq : p.quarter*4=1) (final : Fin 256 → K)
    (received : K → K) (raw : Schedule D q → K → RawRounds (K := K) 3 256)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0<q) (hcount : q≤D.card) :
    suffixProbability p hq final received raw A G≤
      compatibleMoment p final received D q+(q:ℚ)/G.card+18/A.card := by
  have hs := schedules_nonempty D q hcount
  by_cases priorZero : p.prior final=0
  · let E := matching D q (fun x => lineEval final x=received x)
    have bound := avg_exception univ E hs (subset_univ _)
      (fun s => avg G (fun rho =>
        (tail p hq final (fun j => (s j : K)) received rho (raw s rho)).prob A))
      ((q:ℚ)/G.card+18/A.card) (by positivity)
      (fun s _ => avg_le G hg _ _ (fun rho _ => (rounds_unit A ha _).2)) (by
        intro s _ outside
        apply schedule_false_bound p hq final received raw s A G ha hg hpos
        right
        intro zero
        apply outside
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        intro j
        have value := congrFun zero j
        change lineEval final (s j : K)-received (s j : K)=0 at value
        exact sub_eq_zero.mp value)
    rw [card_univ] at bound
    dsimp only [E] at bound
    rw [ordered_matching_ratio] at bound
    simpa only [suffixProbability, compatibleMoment, if_pos priorZero,
      matchingRatio, add_assoc] using bound
  · have bound := avg_le univ hs _ _ (fun s _ =>
      schedule_false_bound p hq final received raw s A G ha hg hpos (Or.inl priorZero))
    simpa only [suffixProbability, compatibleMoment, if_neg priorZero, zero_add] using bound

theorem avg_mono {I : Type*} (S : Finset I) (f g : I → ℚ)
    (h : ∀ i∈S, f i≤g i) : avg S f≤avg S g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

theorem avg_add {I : Type*} (S : Finset I) (f g : I → ℚ) :
    avg S (fun i => f i+g i)=avg S f+avg S g := by
  simp only [avg, Finset.sum_add_distrib, add_div]

theorem avg_constant {I : Type*} (S : Finset I) (nonempty : S.Nonempty) (c : ℚ) :
    avg S (fun _ => c)=c := by
  have card : (S.card:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt nonempty.card_pos
  simp only [avg, Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c card

/-- The event is determined at the entire pre-query prefix. No conditioning
changes the law of earlier challenges; its indicator remains in both means. -/
theorem supported_bound {I : Type*} (S : Finset I) {D : Finset K} {q : Nat}
    (p : I → Prefix (K := K)) (hq : ∀ i, (p i).quarter*4=1)
    (final : I → Fin 256 → K) (received : I → K → K)
    (raw : I → Schedule D q → K → RawRounds (K := K) 3 256)
    (event : I → Prop) (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0<q) (hcount : q≤D.card) :
    avg S (fun i => if event i then
      suffixProbability (p i) (hq i) (final i) (received i) (raw i) A G else 0)≤
    avg S (fun i => if event i then compatibleMoment (p i) (final i) (received i) D q else 0)+
      ((q:ℚ)/G.card+18/A.card)*avg S (fun i => if event i then 1 else 0) := by
  have pointwise := avg_mono S _ _ (fun i _ => show
      (if event i then suffixProbability (p i) (hq i) (final i) (received i) (raw i) A G else 0)≤
      (if event i then compatibleMoment (p i) (final i) (received i) D q else 0)+
        ((q:ℚ)/G.card+18/A.card)*(if event i then 1 else 0) by
    by_cases h : event i
    · simpa only [if_pos h,mul_one,add_assoc] using
        suffix_bound (p i) (hq i) (final i) (received i) (raw i) A G ha hg hpos hcount
    · simp only [if_neg h,mul_zero,zero_add,le_refl])
  rw [avg_add] at pointwise
  have factor : avg S (fun i => ((q:ℚ)/G.card+18/A.card)*(if event i then 1 else 0))=
      ((q:ℚ)/G.card+18/A.card)*avg S (fun i => if event i then 1 else 0) := by
    simp only [avg,← Finset.mul_sum,mul_div_assoc]
  rw [factor] at pointwise
  exact pointwise

/-- The actual causal game: the first compact response knows tau, not alpha;
the final knows both, not queries. The oracle may have arbitrary support B=D.
No extra 6/|A| first-repair term is charged by this suffix reduction. -/
theorem causal_supported_bound {D B : Finset K} {q : Nat}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (oracle : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (event : K → K → Prop) (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0<q) (hcount : q≤D.card) :
    avg G (fun tau => avg A (fun alpha => if event tau alpha then
      (after pre hq oracle s tau alpha).prob A G else 0))≤
    avg G (fun tau => avg A (fun alpha => if event tau alpha then
      compatibleMoment (atFold pre s tau alpha) (s.final tau alpha)
        (oracle.folded alpha) D q else 0))+(q:ℚ)/G.card+18/A.card := by
  have localBound (tau : K) :
      avg A (fun alpha => if event tau alpha then
        (after pre hq oracle s tau alpha).prob A G else 0)≤
      avg A (fun alpha => if event tau alpha then
        compatibleMoment (atFold pre s tau alpha) (s.final tau alpha)
          (oracle.folded alpha) D q else 0)+((q:ℚ)/G.card+18/A.card) := by
    have h := supported_bound A (fun alpha => atFold pre s tau alpha)
      (fun _ => hq) (s.final tau) (fun alpha => oracle.folded alpha)
      (s.rawTail tau) (event tau) A G ha hg hpos hcount
    have mass : avg A (fun alpha => if event tau alpha then (1:ℚ) else 0)≤1 :=
      avg_le A ha _ _ (fun alpha _ => by split_ifs <;> norm_num)
    have nonneg : (0:ℚ)≤(q:ℚ)/G.card+18/A.card := by positivity
    have reduce := mul_le_mul_of_nonneg_left mass nonneg
    rw [mul_one] at reduce
    exact h.trans (add_le_add (le_refl _) reduce)
  have h := avg_mono G _ _ (fun tau _ => localBound tau)
  rw [avg_add,avg_constant G hg] at h
  simpa only [add_assoc] using h

#print axioms schedule_false_bound
#print axioms suffix_bound
#print axioms supported_bound
#print axioms causal_supported_bound
end
end AspisV8.RelationCompatibleMoment
