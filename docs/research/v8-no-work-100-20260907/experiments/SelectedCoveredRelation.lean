import QuotientFamilySelected
import CoveredFirstCollision
import ReferenceIndependentRelation
import SelectedOutsideQuery

/-! Joint arbitrary-oracle rejection unless the actual adaptive final has
an image-and-ordinary-row-correct representative in the literal quotient
family. Only early collision events are multiplied by its cardinality.
One actual shifted query batch and three later repairs are charged once.
Correct quotient representation is NOT original-component/payment recovery. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 400000
namespace AspisV8.CoveredRelationAux
open AspisV8.FirstImageDiscrepancy AspisV8.PostQueryFunctional
open AspisV8.ReferenceIndependentRelation AspisV8.CausalOrderedRelation
open AspisV5ComponentCConcreteFoldLinearity
variable {K : Type*} [Field K] [DecidableEq K]
theorem ite_decider_irrel {V : Type*} {P : Prop} (d e : Decidable P) (x y : V) :
    @ite V P d x y=@ite V P e x y := by
  rw [Subsingleton.elim d e]
theorem prior_at_fold {D : Finset K} {q : Nat} (pre : Before (K := K))
    (s : Strategy D q) (Q : Fin 1024 → K) (tau alpha : K) :
    (atFold pre s tau alpha).prior (coefficientFoldLayer 256 alpha Q)=
      ((replaceBefore pre Q).firstError tau (s.firstResponse tau)).eval alpha :=
  (firstError_eval (replaceBefore pre Q) tau (s.firstResponse tau) alpha).symm
end AspisV8.CoveredRelationAux

namespace AspisV8.SelectedCoveredRelation
open Finset
open AspisV8.SelectedReceivedOracle AspisV8.QuotientFamilySelected
open AspisV8.FirstImageDiscrepancy AspisV8.ShiftedRowPrefix
open AspisV8.PostQueryFunctional AspisV8.CausalOrderedRelation
open AspisV8.ReferenceIndependentRelation AspisV8.RelationCompatibleMoment
open AspisV8.JointImageGame AspisV8.OffFamilyIntersection
open AspisV8.TwoTailQueryBound
open AspisV5ComponentCConcreteFoldLinearity
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance indexFintype : Fintype (Fin 262144) :=
  SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat
    (SimplexCategory.mk 262143)
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

def badAnchor (rows : Rows (K := K)) (Q : Fin 1024 → K) : Prop :=
  Q ⟨1023,by decide⟩≠0 ∨
    rows.b*Q ⟨1022,by decide⟩-rows.c*Q ⟨1021,by decide⟩≠0 ∨
      (replaceRows rows Q).errors≠0

def badFamily (rows : Rows (K := K)) (received : Fin 1048576 → K) :
    Finset (Fin 1024 → K) := (literalFamily received).filter (badAnchor rows)

def goodCovered (rows : Rows (K := K)) (received : Fin 1048576 → K)
    (alpha : K) (final : Fin 256 → K) : Prop :=
  ∃ Q∈literalFamily received, ¬badAnchor rows Q ∧ final=coefficientFoldLayer 256 alpha Q

def firstCollision {q : Nat} (rows : Rows (K := K))
    (strategy : K → Strategy domain q) (Q : Fin 1024 → K)
    (kappa tau alpha : K) : Prop :=
  (((replaceRows rows Q).before kappa).firstError tau
    ((strategy kappa).firstResponse tau)).eval alpha=0

def collisionSum {q : Nat} (rows : Rows (K := K)) (received : Fin 1048576 → K)
    (strategy : K → Strategy domain q) (kappa tau alpha : K) : ℚ :=
  ∑ Q∈badFamily rows received, if firstCollision rows strategy Q kappa tau alpha then 1 else 0

/-- Reference replacement leaves actual weights/scalar unchanged; evaluate
the real carried discrepancy at the represented final, not an assumed law. -/
theorem prior_at_fold {q : Nat} (rows : Rows (K := K))
    (strategy : K → Strategy domain q) (Q : Fin 1024 → K) (kappa tau alpha : K) :
    (atFold (rows.before kappa) (strategy kappa) tau alpha).prior
      (coefficientFoldLayer 256 alpha Q)=
    (((replaceRows rows Q).before kappa).firstError tau
      ((strategy kappa).firstResponse tau)).eval alpha := by
  rw [replaceRows_before]
  exact CoveredRelationAux.prior_at_fold (rows.before kappa) (strategy kappa) Q tau alpha

theorem avg_sum {I J : Type*} (S : Finset I) (F : Finset J) (f : I → J → ℚ) :
    avg S (fun i => ∑ j∈F, f i j)=∑ j∈F, avg S (fun i => f i j) := by
  unfold avg
  rw [Finset.sum_comm]
  exact Finset.sum_div F _ _

theorem collision_sum_bound {q : Nat} (rows : Rows (K := K))
    (quarter : rows.quarter*4=1) (received : Fin 1048576 → K)
    (strategy : K → Strategy domain q) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) :
    avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
      collisionSum rows received strategy kappa tau alpha)))≤
      99*(3/(G.card:ℚ)+6/(A.card:ℚ)) := by
  unfold collisionSum
  simp_rw [avg_sum]
  have each : (∑ Q∈badFamily rows received,
      avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
        if firstCollision rows strategy Q kappa tau alpha then (1:ℚ) else 0))))≤
      ∑ Q∈badFamily rows received, (3/(G.card:ℚ)+6/(A.card:ℚ)) := by
    apply Finset.sum_le_sum
    intro Q member
    have h := CoveredFirstCollision.strategy_bound
      (replaceRows rows Q) quarter strategy A G ha hg (Finset.mem_filter.mp member).2
    refine le_trans (le_of_eq ?_) h
    apply congrArg (avg G)
    funext kappa
    apply congrArg (avg G)
    funext tau
    apply congrArg (avg A)
    funext alpha
    exact CoveredRelationAux.ite_decider_irrel _ _ _ _
  have card : (badFamily rows received).card≤99 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (literalFamily_card_le_99 received)
  have ratCard : ((badFamily rows received).card:ℚ)≤99 := by exact_mod_cast card
  simp only [Finset.sum_const,nsmul_eq_mul] at each
  exact each.trans (mul_le_mul_of_nonneg_right ratCard (by positivity))

/-- If a represented final lacks ANY good representative, every chosen
representative is bad. Actual zero prior then gives a counted early collision.
No uniqueness, retrospective fixing, or received-word polynomiality premise. -/
theorem local_moment_bound {q : Nat} (rows : Rows (K := K))
    (received : Fin 1048576 → K) (strategy : K → Strategy domain q)
    (kappa tau alpha : K) (count : q≤262144) :
    (if ¬goodCovered rows received alpha ((strategy kappa).final tau alpha) then
      compatibleMoment (atFold (rows.before kappa) (strategy kappa) tau alpha)
        ((strategy kappa).final tau alpha)
        ((oracle rows.referenceQ received).folded alpha) domain q else 0)≤
    (if SelectedOutsideQuery.outside received alpha ((strategy kappa).final tau alpha) then
      beta 262144 q (matchingSupport univ received alpha ((strategy kappa).final tau alpha)).card
      else 0)+collisionSum rows received strategy kappa tau alpha := by
  have sums : 0≤collisionSum rows received strategy kappa tau alpha := by
    apply Finset.sum_nonneg
    intro Q _
    split_ifs <;> norm_num
  have ratioNN := beta_nonneg 262144 q
    (matchingSupport univ received alpha ((strategy kappa).final tau alpha)).card
  by_cases missing : ¬goodCovered rows received alpha ((strategy kappa).final tau alpha)
  · simp only [if_pos missing,compatibleMoment,SelectedOutsideQuery.actual_matching_ratio]
    by_cases prior : (atFold (rows.before kappa) (strategy kappa) tau alpha).prior
        ((strategy kappa).final tau alpha)=0
    · simp only [if_pos prior]
      by_cases out : SelectedOutsideQuery.outside received alpha ((strategy kappa).final tau alpha)
      · simp only [if_pos out]
        exact le_add_of_nonneg_right sums
      · simp only [if_neg out,zero_add]
        have covered : CoveredAt univ received 9558 alpha ((strategy kappa).final tau alpha) :=
          Classical.not_not.mp out
        obtain ⟨Q,member,represented⟩ := covered
        have qm := (mem_literalFamily received Q).mpr member
        have bad : badAnchor rows Q := by
          by_contra good
          exact missing ⟨Q,qm,good,represented⟩
        have coll : firstCollision rows strategy Q kappa tau alpha := by
          rw [represented,prior_at_fold] at prior
          exact prior
        have term : (1:ℚ)≤collisionSum rows received strategy kappa tau alpha := by
          have single := Finset.single_le_sum
            (f := fun Q => if firstCollision rows strategy Q kappa tau alpha then (1:ℚ) else 0)
            (fun Q (_ : Q∈badFamily rows received) => by split_ifs <;> norm_num)
            (Finset.mem_filter.mpr ⟨qm,bad⟩)
          simp only [if_pos coll] at single
          unfold collisionSum
          linarith only [single]
        have size : (matchingSupport univ received alpha ((strategy kappa).final tau alpha)).card≤262144 :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq SelectedOutsideQuery.index_univ_card
        exact (beta_unit _ _ _ count size).trans term
    · simp only [if_neg prior]
      split_ifs <;> linarith
  · simp only [if_neg missing]
    split_ifs <;> linarith

def missingGoodProbability {q : Nat} (rows : Rows (K := K))
    (quarter : rows.quarter*4=1) (received : Fin 1048576 → K)
    (strategy : K → Strategy domain q) (A G : Finset K) : ℚ :=
  avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    if ¬goodCovered rows received alpha ((strategy kappa).final tau alpha) then
      (after (rows.before kappa) quarter (oracle rows.referenceQ received)
        (strategy kappa) tau alpha).prob A G else 0)))

/-- The complete selected compact suffix. The arbitrary R and public rows
precede kappa/tau, response0 precedes alpha, final precedes queries, rho and
later responses remain causal. This excludes only the displayed good-quotient
class, which is NOT asserted to contain an extractable component/payment. -/
theorem no_good_quotient_bound {q : Nat} (rows : Rows (K := K))
    (quarter : rows.quarter*4=1) (received : Fin 1048576 → K)
    (strategy : K → Strategy domain q) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (positive : 0<q) (count : q≤262144) :
    missingGoodProbability rows quarter received strategy A G≤
      SelectedOutsideQuery.ceiling q A+99*(3/(G.card:ℚ)+6/(A.card:ℚ))+
        (q:ℚ)/G.card+18/A.card := by
  let moment := fun kappa tau alpha =>
    if ¬goodCovered rows received alpha ((strategy kappa).final tau alpha) then
      compatibleMoment (atFold (rows.before kappa) (strategy kappa) tau alpha)
        ((strategy kappa).final tau alpha)
        ((oracle rows.referenceQ received).folded alpha) domain q else 0
  have suffix := avg_mono G _ _ (fun kappa _ =>
    causal_supported_bound (rows.before kappa) quarter (oracle rows.referenceQ received)
      (strategy kappa) (fun tau alpha =>
        ¬goodCovered rows received alpha ((strategy kappa).final tau alpha))
      A G ha hg positive (by rwa [domain_card]))
  have suffix' : missingGoodProbability rows quarter received strategy A G≤
    avg G (fun kappa => avg G (fun tau => avg A (moment kappa tau))+
      (q:ℚ)/G.card+18/A.card) := by
    refine le_trans (le_of_eq ?_) (le_trans suffix (le_of_eq ?_))
    · unfold missingGoodProbability
      apply congrArg (avg G)
      funext kappa
      apply congrArg (avg G)
      funext tau
      apply congrArg (avg A)
      funext alpha
      exact CoveredRelationAux.ite_decider_irrel _ _ _ _
    · apply congrArg (avg G)
      funext kappa
      apply congrArg (fun value : ℚ => value+(q:ℚ)/G.card+18/A.card)
      apply congrArg (avg G)
      funext tau
      apply congrArg (avg A)
      funext alpha
      exact CoveredRelationAux.ite_decider_irrel _ _ _ _
  rw [avg_add,avg_add,avg_constant G hg,avg_constant G hg] at suffix'
  have moments := avg_mono G _ _ (fun kappa _ => avg_mono G _ _
    (fun tau _ => avg_mono A _ _ (fun alpha _ =>
      local_moment_bound rows received strategy kappa tau alpha count)))
  simp_rw [avg_add] at moments
  have outside := avg_le G hg _ _ (fun kappa _ => avg_le G hg _ _
    (fun tau _ => SelectedOutsideQuery.pointwise_bound received
      ((strategy kappa).final tau) A ha q count))
  have collisions := collision_sum_bound rows quarter received strategy A G ha hg
  change avg G (fun kappa => avg G (fun tau => avg A (moment kappa tau)))≤_ at moments
  exact suffix'.trans (by linarith)

#print axioms prior_at_fold
#print axioms collision_sum_bound
#print axioms local_moment_bound
#print axioms no_good_quotient_bound
end
end AspisV8.SelectedCoveredRelation
