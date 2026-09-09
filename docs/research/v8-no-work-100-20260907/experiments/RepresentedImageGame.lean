import CausalShiftedRows

/-! Supported-event bounds for the actual constructed compact relation game.
The received word can be arbitrary. On the displayed pre-query event only,
the actual adaptive final equals the fold of a reference fixed before tau
(and before kappa for rows). That equality will be supplied by geometric
coverage, not assumed as an acceptance consequence. Unsupported executions
remain outside this event, not conditioned away. -/
set_option autoImplicit false
namespace AspisV8.RepresentedImageGame
open Polynomial Finset
open AspisV8.JointImageGame AspisV8.CausalOrderedRelation
open AspisV8.FirstImageDiscrepancy AspisV8.PostQueryFunctional
open AspisV8.ShiftedRowPrefix
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]

/-- No agreement assumption is needed: taking the corruption set to be the
whole domain packages any fixed received slots in the existing constructor. -/
def arbitraryOracle (D : Finset K) (Q : Fin 1024 → K)
    (x y : K → K) (slots : K → Fin 4 → K)
    (hx : ∀ t ∈ D, x t ≠ 0) (hy : ∀ t ∈ D, y t ≠ 0)
    (coordinate : ∀ t ∈ D, 2*(x t)^2-1=t) : FixedOracle D D Q where
  x := x
  y := y
  slots := slots
  x_nonzero := hx
  y_nonzero := hy
  coordinate := coordinate
  supported := fun _ ht hn => False.elim (hn ht)

/-- Equal actual and reference finals preserve the nonzero carried error.
Even zero query residuals cannot erase its constant coefficient. Neither
polynomiality of the received word nor a query-matching bound is used. -/
theorem after_represented_wrong_bound {D B : Finset K} {q d : ℕ} {e : K}
    (g : OrderedQueryGame.After D B q d e)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0 < q) (hcount : q ≤ D.card)
    (represented : g.difference=0) (wrong : e≠0) :
    g.prob A G ≤ (q:ℚ)/G.card+18/A.card := by
  have hp : g.prior ≠ 0 := by rw [g.same_prior represented]; exact wrong
  apply avg_le _ (OrderedQueryGame.schedules_nonempty D q hcount)
  intro queries _
  apply avg_polynomial G hg (shifted g.prior (g.residual queries))
    (shifted_nonzero _ _ (Or.inl hp)) q (shifted_degree hpos _ _)
    _ (18/A.card) (by positivity)
    (fun rho _ => (rounds_unit A ha (g.tail queries rho)).2)
  intro rho _ hn
  convert rounds_false_bound A ha (g.tail queries rho) hn using 1 <;> norm_num

/-- `support` is determined after tau/alpha/final but before queries. Its
indicator is averaged in the original experiment, never used to condition
the challenge distribution. Responses and finals can depend on tau. -/
noncomputable def supportedProbability {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (support : K → K → Prop) (A G : Finset K) : ℚ := by
  classical
  exact avg G (fun tau => avg A (fun alpha =>
    if support tau alpha then (after pre hq o s tau alpha).prob A G else 0))

theorem supported_unit {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (support : K → K → Prop) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hcount : q≤D.card) :
    supportedProbability pre hq o s support A G ≤ 1 := by
  classical
  apply avg_le G hg
  intro tau _
  apply avg_le A ha
  intro alpha _
  split_ifs
  · exact CausalOrderedRelation.after_unit pre hq o s tau alpha A G ha hg hcount
  · norm_num

theorem supported_nonneg {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (support : K → K → Prop) (A G : Finset K) (ha : A.Nonempty) :
    0 ≤ supportedProbability pre hq o s support A G := by
  classical
  apply avg_nonneg G
  intro tau _
  apply avg_nonneg A
  intro alpha _
  split_ifs
  · exact avg_nonneg _ _ (fun queries _ => avg_nonneg G _
      (fun rho _ => (rounds_unit A ha ((after pre hq o s tau alpha).tail queries rho)).1))
  · exact le_rfl

theorem represented_first_stage_bound {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (support : K → K → Prop)
    (represented : ∀ tau alpha, support tau alpha →
      s.final tau alpha=(atFold pre s tau alpha).referenceFinal)
    (tau : K) (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0<q) (hcount : q≤D.card)
    (wrong : pre.errorPolynomial.eval tau≠0) :
    (by classical exact avg A (fun alpha =>
      if support tau alpha then (after pre hq o s tau alpha).prob A G else 0)) ≤
        6/A.card+((q:ℚ)/G.card+18/A.card) := by
  classical
  apply avg_polynomial A ha (pre.firstError tau (s.firstResponse tau))
    (firstError_nonzero pre hq tau (s.firstResponse tau) wrong) 6
    (firstError_degree pre tau (s.firstResponse tau)) _ _ (by positivity)
    (by
      intro alpha _
      split_ifs
      · exact CausalOrderedRelation.after_unit pre hq o s tau alpha A G ha hg hcount
      · norm_num)
  intro alpha _ hn
  split_ifs with hs
  · have hd : (after pre hq o s tau alpha).difference=0 := by
      dsimp only [CausalOrderedRelation.after, OrderedPostQueryGame.fromPrefix]
      exact (difference_zero_iff _ _).mpr (represented tau alpha hs)
    exact after_represented_wrong_bound (after pre hq o s tau alpha)
      A G ha hg hpos hcount hd hn
  · positivity

/-- Invalid image or wrong fixed ordinary discrepancy, restricted to represented
finals. The bound counts image mixing and all four relation repairs once. -/
theorem represented_bad_anchor_bound {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (support : K → K → Prop)
    (represented : ∀ tau alpha, support tau alpha →
      s.final tau alpha=(atFold pre s tau alpha).referenceFinal)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0<q) (hcount : q≤D.card)
    (bad : pre.prior≠0 ∨ pre.E1≠0 ∨ pre.E2≠0) :
    supportedProbability pre hq o s support A G ≤ ((q:ℚ)+2)/G.card+24/A.card := by
  classical
  have h := avg_polynomial G hg pre.errorPolynomial
    (AspisV8.RobustImageGame.image_nonzero_any pre.prior pre.E1 pre.E2 bad) 2
    (error_degree pre)
    (fun tau => avg A (fun alpha =>
      if support tau alpha then (after pre hq o s tau alpha).prob A G else 0))
    (6/A.card+((q:ℚ)/G.card+18/A.card)) (by positivity)
    (by
      intro tau _
      apply avg_le A ha
      intro alpha _
      split_ifs
      · exact CausalOrderedRelation.after_unit pre hq o s tau alpha A G ha hg hcount
      · norm_num)
    (fun tau _ hn => represented_first_stage_bound
      pre hq o s support represented tau A G ha hg hpos hcount hn)
  change avg _ _ ≤ _
  convert h using 1 <;> ring

/-- Image validity makes the incoming error independent of tau; there is no
extra image-root charge in the shifted-row branch. -/
theorem represented_image_valid_wrong_bound {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (support : K → K → Prop)
    (represented : ∀ tau alpha, support tau alpha →
      s.final tau alpha=(atFold pre s tau alpha).referenceFinal)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0<q) (hcount : q≤D.card)
    (h1 : pre.E1=0) (h2 : pre.E2=0) (wrong : pre.prior≠0) :
    supportedProbability pre hq o s support A G ≤ (q:ℚ)/G.card+24/A.card := by
  classical
  have h := avg_le G hg
    (fun tau => avg A (fun alpha =>
      if support tau alpha then (after pre hq o s tau alpha).prob A G else 0))
    (6/A.card+((q:ℚ)/G.card+18/A.card))
    (fun tau _ => represented_first_stage_bound
      pre hq o s support represented tau A G ha hg hpos hcount (by
        simpa only [Before.errorPolynomial, imagePolynomial_eval, h1, h2,
          mul_zero, sub_zero] using wrong))
  change avg _ _ ≤ _
  convert h using 1 <;> ring

noncomputable def supportedRowsProbability {D B : Finset K} {q : ℕ}
    (rows : Rows (K := K)) (hq : rows.quarter*4=1)
    (oracle : FixedOracle D B rows.referenceQ) (strategy : K → Strategy D q)
    (support : K → K → K → Prop) (A G : Finset K) : ℚ :=
  avg G (fun kappa => supportedProbability (rows.before kappa) hq
    oracle (strategy kappa) (support kappa) A G)

theorem represented_wrong_rows_bound {D B : Finset K} {q : ℕ}
    (rows : Rows (K := K)) (hq : rows.quarter*4=1)
    (oracle : FixedOracle D B rows.referenceQ) (strategy : K → Strategy D q)
    (support : K → K → K → Prop)
    (represented : ∀ kappa tau alpha, support kappa tau alpha →
      (strategy kappa).final tau alpha=
        (atFold (rows.before kappa) (strategy kappa) tau alpha).referenceFinal)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0<q) (hcount : q≤D.card)
    (image1 : rows.referenceQ ⟨1023, by decide⟩=0)
    (image2 : rows.b*rows.referenceQ ⟨1022, by decide⟩-
      rows.c*rows.referenceQ ⟨1021, by decide⟩=0)
    (wrong : rows.errors≠0) :
    supportedRowsProbability rows hq oracle strategy support A G ≤
      ((q:ℚ)+3)/G.card+24/A.card := by
  have h := avg_polynomial G hg rows.errorPolynomial
    (ShiftedRowPrefix.error_nonzero rows wrong) 3 (ShiftedRowPrefix.error_degree rows)
    (fun kappa => supportedProbability (rows.before kappa) hq
      oracle (strategy kappa) (support kappa) A G)
    ((q:ℚ)/G.card+24/A.card) (by positivity)
    (fun kappa _ => supported_unit (rows.before kappa) hq oracle
      (strategy kappa) (support kappa) A G ha hg hcount)
    (by
      intro kappa _ hn
      apply represented_image_valid_wrong_bound (rows.before kappa) hq oracle
        (strategy kappa) (support kappa) (represented kappa) A G ha hg hpos hcount
      · exact image1
      · exact image2
      · rw [before_prior]
        exact hn)
  change avg _ _ ≤ _
  convert h using 1 <;> ring

/-- Disjoint cases are fixed before kappa. Invalid image uses two roots;
valid image plus a wrong ordinary row uses three. Taking the latter uniform
ceiling here is justified by this explicit partition, not by adding terms. -/
theorem represented_image_or_rows_bound {D B : Finset K} {q : ℕ}
    (rows : Rows (K := K)) (hq : rows.quarter*4=1)
    (oracle : FixedOracle D B rows.referenceQ) (strategy : K → Strategy D q)
    (support : K → K → K → Prop)
    (represented : ∀ kappa tau alpha, support kappa tau alpha →
      (strategy kappa).final tau alpha=
        (atFold (rows.before kappa) (strategy kappa) tau alpha).referenceFinal)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0<q) (hcount : q≤D.card)
    (bad : rows.referenceQ ⟨1023, by decide⟩≠0 ∨
      rows.b*rows.referenceQ ⟨1022, by decide⟩-
        rows.c*rows.referenceQ ⟨1021, by decide⟩≠0 ∨ rows.errors≠0) :
    supportedRowsProbability rows hq oracle strategy support A G ≤
      ((q:ℚ)+3)/G.card+24/A.card := by
  by_cases hi : rows.referenceQ ⟨1023, by decide⟩=0 ∧
      rows.b*rows.referenceQ ⟨1022, by decide⟩-
        rows.c*rows.referenceQ ⟨1021, by decide⟩=0
  · apply represented_wrong_rows_bound rows hq oracle strategy support represented
      A G ha hg hpos hcount hi.1 hi.2
    rcases bad with h | h | h
    · exact False.elim (h hi.1)
    · exact False.elim (h hi.2)
    · exact h
  · have h := avg_le G hg
      (fun kappa => supportedProbability (rows.before kappa) hq
        oracle (strategy kappa) (support kappa) A G)
      (((q:ℚ)+2)/G.card+24/A.card) (by
        intro kappa _
        apply represented_bad_anchor_bound (rows.before kappa) hq oracle
          (strategy kappa) (support kappa) (represented kappa) A G ha hg hpos hcount
        right
        by_cases h1 : rows.referenceQ ⟨1023, by decide⟩=0
        · right
          exact fun h2 => hi ⟨h1,h2⟩
        · exact Or.inl h1)
    change avg _ _ ≤ _
    have hc : (0:ℚ) ≤ 1/G.card := by positivity
    have heq : ((q:ℚ)+3)/G.card+24/A.card =
        (((q:ℚ)+2)/G.card+24/A.card)+1/G.card := by ring
    rw [heq]
    exact le_trans h (le_add_of_nonneg_right hc)

#print axioms arbitraryOracle
#print axioms after_represented_wrong_bound
#print axioms supported_nonneg
#print axioms represented_first_stage_bound
#print axioms represented_bad_anchor_bound
#print axioms represented_image_valid_wrong_bound
#print axioms represented_wrong_rows_bound
#print axioms represented_image_or_rows_bound
end AspisV8.RepresentedImageGame
