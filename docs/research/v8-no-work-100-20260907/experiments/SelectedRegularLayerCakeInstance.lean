import CommonRegularRow
import GenericRegularLayerCake
import SelectedRegularLowSupport

/-! Source-review draft: construct one analysis representative per factor/gamma,
not a pre-alpha prover final. The support table is independent of all later
kappa/tau/alpha choices. Z-root histories contribute zero without deleting or
renormalizing Gamma. Factor occurrences retain their multiset multiplicities.
This leaf integrates only the matching moment; the shared suffix charge and
the outer kappa/tau averages remain separate interfaces.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedRegularLayerCakeInstance
open Polynomial Finset
open AspisV8.TwoTailQueryBound AspisV8.GenericRegularLayerCake
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

namespace Generic

theorem mean_multiset {I J : Type*} (s : Multiset I) (S : Finset J)
    (value : I → J → ℚ) :
    mean S (fun j => (s.map (fun i => value i j)).sum) =
      (s.map (fun i => mean S (value i))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.map_zero, Multiset.sum_zero, mean,
      Finset.sum_const_zero, zero_div]
  | @cons i s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, mean_add, ih]

theorem mean_aggregate {I J : Type*} (s : Multiset I) (S : Finset J)
    (value : I → J → ℚ) :
    mean S (fun j => (s.map (fun i => value i j)).sum) =
      aggregate s S value / S.card := by
  induction s using Multiset.induction_on with
  | empty => simp only [aggregate, Multiset.map_zero, Multiset.sum_zero, mean,
      Finset.sum_const_zero, zero_div]
  | @cons i s ih =>
      simp only [aggregate, Multiset.map_cons, Multiset.sum_cons, add_div] at ih ⊢
      rw [mean_add, ih]
      rfl

theorem averaged_union_le {I J AType : Type*} (s : Multiset I)
    (Gamma : Finset J) (A : Finset AType)
    (score : I → J → AType → ℚ) (value : J → AType → ℚ)
    (pointwise : ∀ gamma ∈ Gamma, ∀ alpha ∈ A,
      value gamma alpha ≤ (s.map (fun F => score F gamma alpha)).sum) :
    mean Gamma (fun gamma => mean A (value gamma)) ≤
      aggregate s Gamma (fun F gamma => mean A (score F gamma)) / Gamma.card := by
  apply (mean_mono Gamma _ _ (fun gamma inside =>
    mean_mono A _ _ (fun alpha inA => pointwise gamma inside alpha inA))).trans_eq
  have inner : (fun gamma => mean A (fun alpha =>
      (s.map (fun F => score F gamma alpha)).sum)) =
      (fun gamma => (s.map (fun F => mean A (score F gamma))).sum) := by
    funext gamma
    exact mean_multiset s A (fun F alpha => score F gamma alpha)
  rw [inner]
  exact mean_aggregate s Gamma (fun F gamma => mean A (score F gamma))

end Generic

open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisV5ComponentCConcreteFoldLinearity
open AspisV8.SelectedReceivedOracle AspisV8.CausalCoveredRecovery
open AspisV8.SelectedHigherYBranch AspisV8.CausalHigherYClassification
open AspisV8.SelectedHigherYHighSupport AspisV8.SelectedRegularLowSupport
open AspisV8.SelectedHigherYRegularTail AspisV8.SelectedRegularTailSum
open AspisV8.SelectedFactorCoherence AspisV8.SelectedOODGate
open AspisV8.ComponentOODBinding AspisV8.FactorIdentityCover
open AspisV8.CausalOrderedRelation AspisV8.RelationCompatibleMoment
open AspisV8.SingularOODFamily

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
attribute [local irreducible] curvePrimeFactors

def retained {q : Nat} (e : Execution q) (F : TrivariatePolynomial K) : Prop :=
  Retained (point e.data) (fun row => CurveOODGate.answerCurve (answers e.data row)) F

def factorEvent {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (F : TrivariatePolynomial K) (gamma kappa tau alpha : K) : Prop :=
  Z.eval gamma ≠ 0 ∧ retained e F ∧ lowRegularPrefix e F r gamma kappa tau alpha

/-- All later histories are existentially quantified in this fixed table.
There is no actual-final choice in the table's index. -/
def Active {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (F : TrivariatePolynomial K) (gamma : K) : Prop :=
  ∃ kappa tau alpha, factorEvent e r Z F gamma kappa tau alpha

theorem active_qualified {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (F : TrivariatePolynomial K) (gamma : K) (active : Active e r Z F gamma) :
    ∃ Q, Qualified e.c1 e.c2 e.data F gamma Q := by
  obtain ⟨kappa, tau, alpha, _, _, _, Q, qualified, _⟩ := active
  exact ⟨Q, qualified⟩

/-- Total on every factor/gamma pair. Zero is only an inactive placeholder;
no qualification, image or support claim is made for that placeholder. -/
def representative {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (F : TrivariatePolynomial K) (gamma : K) : Fin 1024 → K :=
  if h : Active e r Z F gamma then Classical.choose (active_qualified e r Z F gamma h)
  else 0

def support {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (F : TrivariatePolynomial K) (gamma : K) : Nat :=
  if Active e r Z F gamma then fibreCount (e.raw gamma) (representative e r Z F gamma)
  else 0

theorem representative_qualified {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (F : TrivariatePolynomial K) (gamma : K) (active : Active e r Z F gamma) :
    Qualified e.c1 e.c2 e.data F gamma (representative e r Z F gamma) := by
  simp only [representative, dif_pos active]
  exact Classical.choose_spec (active_qualified e r Z F gamma active)

theorem active_regular {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (F : TrivariatePolynomial K) (gamma : K) (active : Active e r Z F gamma) :
    (FactorCoherence.derivativeCurve F (point e.data r)
      (CurveOODGate.answerCurve (answers e.data r))).eval gamma ≠ 0 := by
  obtain ⟨kappa, tau, alpha, _, _, _, Q, _, _, _, regular⟩ := active
  exact regular

/-- The actual selected final is identified only when the event holds.
It still depends on tau and alpha in the literal strategy. -/
theorem representative_final {q : Nat} (e : Execution q) (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (r : Fin 2) (Z : K[X])
    (F : TrivariatePolynomial K) (gamma kappa tau alpha : K)
    (selected : factorEvent e r Z F gamma kappa tau alpha) :
    (e.strategy gamma kappa).final tau alpha =
      coefficientFoldLayer 256 alpha (representative e r Z F gamma) := by
  have active : Active e r Z F gamma := ⟨kappa, tau, alpha, selected⟩
  exact SelectedRegularQueryBridge.fixed_regular_final e checked circles west F r gamma
    (representative e r Z F gamma) (representative_qualified e r Z F gamma active)
    kappa tau alpha selected.2.2.2

theorem representative_bounds {q : Nat} (e : Execution q) (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (r : Fin 2) (Z : K[X])
    (F : TrivariatePolynomial K) (member : F ∈ higherFactors (parent e.c1 e.c2))
    (gamma : K) (active : Active e r Z F gamma) :
    9558 ≤ support e r Z F gamma ∧ support e r Z F gamma ≤ 200807 := by
  obtain ⟨factor, higher⟩ := Multiset.mem_filter.mp member
  have history := active
  obtain ⟨kappa, tau, alpha, _, keep, selected⟩ := history
  obtain ⟨Q, qualified, _, lower, upper⟩ :=
    low_regular_witness e F factor keep higher r gamma kappa tau alpha selected
  have same := SelectedOriginalInjectivity.regular_qualified_unique e.c1 e.c2 e.data
    checked circles west F gamma (representative e r Z F gamma) Q
    (representative_qualified e r Z F gamma active) qualified r
    (active_regular e r Z F gamma active)
  simpa only [support, if_pos active, same] using And.intro lower upper

def prefixMoment {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) : ℚ :=
  compatibleMoment (atFold ((e.rows gamma).before kappa)
    (e.strategy gamma kappa) tau alpha) ((e.strategy gamma kappa).final tau alpha)
    ((oracle 0 (e.raw gamma)).folded alpha) domain q

def score {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (kappa tau : K) (F : TrivariatePolynomial K) (gamma alpha : K) : ℚ :=
  if factorEvent e r Z F gamma kappa tau alpha then prefixMoment e gamma kappa tau alpha
  else 0

theorem prefixMoment_nonneg {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) :
    0 ≤ prefixMoment e gamma kappa tau alpha := by
  unfold prefixMoment compatibleMoment matchingRatio
  split_ifs <;> positivity

theorem inactive_score {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (F : TrivariatePolynomial K) (gamma : K) (inactive : ¬Active e r Z F gamma)
    (kappa tau alpha : K) : score e r Z kappa tau F gamma alpha = 0 := by
  apply if_neg
  intro selected
  exact inactive ⟨kappa, tau, alpha, selected⟩

/-- Exact source moment for the constructed table, including inactive pairs. -/
theorem score_moment {q : Nat} (e : Execution q) (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (r : Fin 2) (Z : K[X])
    (F : TrivariatePolynomial K) (gamma kappa tau : K)
    (A : Finset K) (nonempty : A.Nonempty) (count : q ≤ 262144) :
    mean A (score e r Z kappa tau F gamma) ≤ if Active e r Z F gamma then
      beta 262144 q (support e r Z F gamma) +
        (1-beta 262144 q (support e r Z F gamma))*epsilon A else 0 := by
  by_cases active : Active e r Z F gamma
  · have history := active
    obtain ⟨kappa', tau', alpha', nonroot, keep, _⟩ := history
    have scores : score e r Z kappa tau F gamma = fun alpha =>
        if lowRegularPrefix e F r gamma kappa tau alpha then
          prefixMoment e gamma kappa tau alpha else 0 := by
      funext alpha
      by_cases low : lowRegularPrefix e F r gamma kappa tau alpha
      · have event : factorEvent e r Z F gamma kappa tau alpha := ⟨nonroot, keep, low⟩
        simp only [score, if_pos event, if_pos low]
      · have absent : ¬factorEvent e r Z F gamma kappa tau alpha :=
          fun event => low event.2.2
        simp only [score, if_neg absent, if_neg low]
    have bound := low_regular_moment e checked circles west F r gamma
      (representative e r Z F gamma) (representative_qualified e r Z F gamma active)
      kappa tau A nonempty count
    rw [full_query_mass] at bound
    rw [scores, if_pos active]
    simpa only [mean, JointImageGame.avg, prefixMoment, support, if_pos active,
      beta, epsilon] using bound
  · have zero : score e r Z kappa tau F gamma = fun _ => 0 := by
      funext alpha
      exact inactive_score e r Z F gamma active kappa tau alpha
    rw [zero, mean_constant A nonempty 0, if_neg active]

/-- Every active threshold enters the SAME-Q, SAME-row old V7 support tail. -/
theorem table_tail_le {q : Nat} (e : Execution q) (checked : e.data.Checked)
    (r : Fin 2) (Z : K[X]) (Gamma : Finset K) (m : Nat) :
    tail (higherFactors (parent e.c1 e.c2)) Gamma (Active e r Z) (support e r Z) m ≤
      tailSum e.c1 e.c2 e.data r Gamma (4*m-2) := by
  apply Multiset.sum_map_le_sum_map
  intro F _
  by_cases keep : retained e F
  · change (Gamma.filter fun gamma => Active e r Z F gamma ∧
      m ≤ support e r Z F gamma).card ≤
      if retained e F then (supportGammas e.c1 e.c2 e.data F r Gamma (4*m-2)).card else 0
    rw [if_pos keep]
    apply Finset.card_le_card
    intro gamma member
    obtain ⟨inside, active, many⟩ := Finset.mem_filter.mp member
    apply regular_fibre_tail_mem e checked F r Gamma gamma inside
      (representative e r Z F gamma) (representative_qualified e r Z F gamma active)
      (active_regular e r Z F gamma active) m
    simpa only [support, if_pos active] using many
  · have empty : (Gamma.filter fun gamma => Active e r Z F gamma ∧
        m ≤ support e r Z F gamma) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro gamma member
      obtain ⟨_, ⟨kappa, tau, alpha, _, retained, _⟩, _⟩ := Finset.mem_filter.mp member
      exact keep retained
    change (Gamma.filter fun gamma => Active e r Z F gamma ∧
      m ≤ support e r Z F gamma).card ≤
      if retained e F then (supportGammas e.c1 e.c2 e.data F r Gamma (4*m-2)).card else 0
    simp only [empty, Finset.card_empty, if_neg keep, le_refl]

def tailBudget (m : Nat) : Nat := (1048576*239599331)/(4*m-1026)

theorem table_tail_bound {q : Nat} (e : Execution q) (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (r : Fin 2) (Z : K[X])
    (Gamma : Finset K) (m : Nat) (lower : 9558 ≤ m) :
    tail (higherFactors (parent e.c1 e.c2)) Gamma (Active e r Z) (support e r Z) m ≤
      tailBudget m := by
  have positive : 0 < 4*m-1026 := by omega
  have same : (4*m-2)-1024 = 4*m-1026 := by omega
  have source := tail_sum_bound e.c1 e.c2 e.data checked circles west r Gamma (4*m-2)
  rw [same] at source
  apply (Nat.le_div_iff_mul_le positive).mpr
  have bound := (Nat.mul_le_mul_left (4*m-1026)
    (table_tail_le e checked r Z Gamma m)).trans source
  simpa only [Nat.mul_comm] using bound

def integratedBudget (q : Nat) (Gamma A : Finset K) : ℚ :=
  (1-epsilon A)*layer (beta 262144 q) 9558 200807 tailBudget/Gamma.card + 3/A.card

/-- Actual source instantiation of the conservative layer cake. No Q,
support table, tail inequality or moment bound is supplied by the caller. -/
theorem factor_moment_bound {q : Nat} (e : Execution q) (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (r : Fin 2) (Z : K[X])
    (Gamma A : Finset K) (gammaNonempty : Gamma.Nonempty) (alphaNonempty : A.Nonempty)
    (largeGamma : 6752623450 ≤ Gamma.card) (count : q ≤ 262144) (kappa tau : K) :
    aggregate (higherFactors (parent e.c1 e.c2)) Gamma
      (fun F gamma => mean A (score e r Z kappa tau F gamma))/Gamma.card ≤
      integratedBudget q Gamma A := by
  apply factor_gamma_alpha_conservative (higherFactors (parent e.c1 e.c2)) Gamma A
    (Active e r Z) (support e r Z) (score e r Z kappa tau)
    262144 q 9558 200807 A.card tailBudget gammaNonempty alphaNonempty rfl (by omega)
  · exact selected_minimum_floor.le.trans largeGamma
  · intro F member gamma _ active
    exact representative_bounds e checked circles west r Z F member gamma active
  · intro m range
    exact table_tail_bound e checked circles west r Z Gamma m (Finset.mem_Icc.mp range).1
  · intro F _ gamma _
    exact score_moment e checked circles west r Z F gamma kappa tau A alphaNonempty count

def unionScore {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (gamma kappa tau alpha : K) : ℚ :=
  if Z.eval gamma ≠ 0 ∧ regularLowUnion e r gamma kappa tau alpha then
    prefixMoment e gamma kappa tau alpha else 0

/-- Explicit witness union bound; neither disjointness nor unique factors
is assumed. Each multiset occurrence contributes a nonnegative score. -/
theorem union_score_le {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (gamma kappa tau alpha : K) :
    unionScore e r Z gamma kappa tau alpha ≤
      ((higherFactors (parent e.c1 e.c2)).map
        (fun F => score e r Z kappa tau F gamma alpha)).sum := by
  have nonnegative (F : TrivariatePolynomial K) : 0 ≤ score e r Z kappa tau F gamma alpha := by
    unfold score
    split_ifs
    · exact prefixMoment_nonneg e gamma kappa tau alpha
    · exact le_refl _
  have allNonnegative : ∀ v ∈ ((higherFactors (parent e.c1 e.c2)).map
      (fun F => score e r Z kappa tau F gamma alpha)), 0 ≤ v := by
    intro v member
    obtain ⟨F, _, rfl⟩ := Multiset.mem_map.mp member
    exact nonnegative F
  by_cases selected : Z.eval gamma ≠ 0 ∧ regularLowUnion e r gamma kappa tau alpha
  · have witness := selected
    obtain ⟨nonroot, F, member, keep, low⟩ := witness
    have event : factorEvent e r Z F gamma kappa tau alpha := ⟨nonroot, keep, low⟩
    have single := Multiset.single_le_sum allNonnegative
      (score e r Z kappa tau F gamma alpha) (Multiset.mem_map.mpr ⟨F, member, rfl⟩)
    simpa only [unionScore, if_pos selected, score, if_pos event] using single
  · simpa only [unionScore, if_neg selected] using Multiset.sum_nonneg allNonnegative

theorem union_moment_bound {q : Nat} (e : Execution q) (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (r : Fin 2) (Z : K[X])
    (Gamma A : Finset K) (gammaNonempty : Gamma.Nonempty) (alphaNonempty : A.Nonempty)
    (largeGamma : 6752623450 ≤ Gamma.card) (count : q ≤ 262144) (kappa tau : K) :
    mean Gamma (fun gamma => mean A (fun alpha => unionScore e r Z gamma kappa tau alpha)) ≤
      integratedBudget q Gamma A := by
  apply (Generic.averaged_union_le (higherFactors (parent e.c1 e.c2)) Gamma A
    (score e r Z kappa tau) (fun gamma alpha => unionScore e r Z gamma kappa tau alpha)
    (fun gamma _ alpha _ => union_score_le e r Z gamma kappa tau alpha)).trans
  exact factor_moment_bound e checked circles west r Z Gamma A gammaNonempty alphaNonempty
    largeGamma count kappa tau

/-- The common row upgrades the literal LOW prefix, not an assumed
regular witness. The very same Q supplies image, factor root and final. -/
theorem guarded_low_regular {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (guard : ∀ gamma, Z.eval gamma ≠ 0 → ∀ F ∈ higherFactors (parent e.c1 e.c2),
      retained e F → (FactorCoherence.derivativeCurve F (point e.data r)
        (CurveOODGate.answerCurve (answers e.data r))).eval gamma ≠ 0)
    (gamma kappa tau alpha : K) (nonroot : Z.eval gamma ≠ 0)
    (low : LowPrefix e gamma kappa tau alpha) : regularLowUnion e r gamma kappa tau alpha := by
  obtain ⟨Q, witness⟩ := (witness_exists_iff e gamma kappa tau alpha).mpr low.1
  obtain ⟨F, member, keep, root, higher⟩ := witness.2.2.2
  have higherMember : F ∈ higherFactors (parent e.c1 e.c2) :=
    Multiset.mem_filter.mpr ⟨member, higher⟩
  have qualified : Qualified e.c1 e.c2 e.data F gamma Q :=
    ⟨witness.1, witness_image e gamma kappa tau alpha Q witness, root⟩
  exact ⟨F, higherMember, keep, low, Q, qualified, witness.2.1, witness.2.2.1,
    guard gamma nonroot F higherMember keep⟩

/-- One pre-gamma row/product guard, and the integrated matching bound for
EVERY later kappa/tau. The finite Gamma is unchanged on both sides. This
does not add its root cost or a suffix repair term to the matching bound. -/
theorem exists_common_row_bound {q : Nat} (e : Execution q) (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (Gamma A : Finset K)
    (gammaNonempty : Gamma.Nonempty) (alphaNonempty : A.Nonempty)
    (largeGamma : 6752623450 ≤ Gamma.card) (count : q ≤ 262144)
    (outside : ¬∀ r, (SelectedSingularOODFamily.obstruction e.c1 e.c2).eval
      (point e.data r)=0) :
    ∃ r : Fin 2, ∃ Z : K[X], Z ≠ 0 ∧ Z.natDegree ≤ 117049 ∧
      (Gamma.filter fun gamma => Z.eval gamma=0).card ≤ 117049 ∧
      (∀ gamma kappa tau alpha, Z.eval gamma ≠ 0 → LowPrefix e gamma kappa tau alpha →
        regularLowUnion e r gamma kappa tau alpha) ∧
      ∀ kappa tau, mean Gamma (fun gamma => mean A (fun alpha =>
        unionScore e r Z gamma kappa tau alpha)) ≤ integratedBudget q Gamma A := by
  obtain ⟨r, Z, nonzero, degree, roots, guard⟩ :=
    CommonRegularRow.selected_common_row e.c1 e.c2 e.data Gamma outside
  refine ⟨r, Z, nonzero, degree, roots, ?_, ?_⟩
  · intro gamma kappa tau alpha nonroot low
    exact guarded_low_regular e r Z guard gamma kappa tau alpha nonroot low
  · intro kappa tau
    exact union_moment_bound e checked circles west r Z Gamma A gammaNonempty alphaNonempty
      largeGamma count kappa tau

#print axioms Generic.averaged_union_le
#print axioms representative_final
#print axioms representative_bounds
#print axioms score_moment
#print axioms table_tail_bound
#print axioms factor_moment_bound
#print axioms union_score_le
#print axioms union_moment_bound
#print axioms guarded_low_regular
#print axioms exists_common_row_bound
end
end AspisV8.SelectedRegularLayerCakeInstance
