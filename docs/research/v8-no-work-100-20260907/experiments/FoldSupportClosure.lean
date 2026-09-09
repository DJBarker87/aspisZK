import SevenAlphaRecovery

/-! Fixed-Q support closure for the actual selected four-slot fold.
Four distinct identified folds agreeing at a fibre recover every raw slot
there. For complete mathematical matching sets this recovers exactly Q's
existing support; the collector benefit is combining differently exposed
per-branch supports. There is no probability or authentication theorem here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.FoldSupportAlgebra
open Polynomial Finset
open AspisV8.ExactFoldRecovery
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation AspisV5FriConcreteEncoderApplicability
noncomputable section
variable {K F : Type*} [Field K] [DecidableEq K] [Field F] [Algebra F K]

/-- Four equal actual folds of two arbitrary words at one fibre identify all
four raw slots. The cubic representations and inverse are proved interfaces. -/
theorem four_folds_identify_slots {m : Nat} (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (left right : Fin (4*m) → K) (i : Fin m)
    (nodes : Finset K) (four : 4≤nodes.card)
    (same : ∀ alpha∈nodes,
      circleFoldLayer m alpha inverse2x inverse2y left i=
        circleFoldLayer m alpha inverse2x inverse2y right i) :
    ∀ slot : Fin 4, left (childIndex i slot)=right (childIndex i slot) := by
  have small (word : Fin (4*m) → K) :
      (foldCurve inverse2x inverse2y word i).degree < nodes.card := by
    have degree : (foldCurve inverse2x inverse2y word i).natDegree < nodes.card := by
      have bounded := foldCurve_degree inverse2x inverse2y word i
      omega
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr degree)
  have curves : foldCurve inverse2x inverse2y left i=
      foldCurve inverse2x inverse2y right i := by
    apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq nodes (small left) (small right)
    intro alpha member
    rw [foldCurve_eval_actual x y inverse2x inverse2y hx hy,
      foldCurve_eval_actual x y inverse2x inverse2y hx hy]
    exact same alpha member
  have decoded : decodedSlots inverse2x inverse2y left i=
      decodedSlots inverse2x inverse2y right i := by
    funext slot
    have h := congrArg (fun p : K[X] => p.coeff slot.val) curves
    simpa only [foldCurve,monomialPolynomial_coeff] using h
  have invert (word : Fin (4*m) → K) :
      radix4Evaluate (y i) (-y i) (x i)
        (decodedSlots inverse2x inverse2y word i)=
          (fun slot => word (childIndex i slot)) := by
    exact radix4Evaluate_radix4Decode (y i) (-y i) (x i)
      (algebraMap F K (inverse2y i)) (-(algebraMap F K (inverse2y i)))
      (algebraMap F K (inverse2x i)) (hy i)
      (by simpa only [neg_mul,mul_neg,neg_neg] using hy i) (hx i) _
  have raw := (invert left).symm.trans
    ((congrArg (radix4Evaluate (y i) (-y i) (x i)) decoded).trans (invert right))
  exact fun slot => congrFun raw slot

#print axioms four_folds_identify_slots
end
end AspisV8.FoldSupportAlgebra

namespace AspisV8.FoldSupportClosure
open Finset
open AspisV8.SevenAlphaRecovery
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCConcreteFoldLinearity AspisV5ComponentCQM31TowerExact
open AspisV5FriConcreteEncoderCommutation
noncomputable section

def Matches (received : Fin 1048576 → QM31Exact) (alpha : QM31Exact)
    (final : Fin 256 → QM31Exact) (i : Fin 262144) : Prop :=
  exactFinalLinear final i=circleFoldLayer 262144 alpha
    (canonicalOneFoldSchedule 0).circleInv2x
    (canonicalOneFoldSchedule 0).circleInv2y received i

def FullSlots (received : Fin 1048576 → QM31Exact) (Q : Fin 1024 → QM31Exact)
    (i : Fin 262144) : Prop :=
  ∀ slot : Fin 4, exactInitialEncoder Q (childIndex i slot)=received (childIndex i slot)

def matchingNodes (received : Fin 1048576 → QM31Exact) (nodes : Finset QM31Exact)
    (final : QM31Exact → Fin 256 → QM31Exact) (i : Fin 262144) : Finset QM31Exact := by
  classical
  exact nodes.filter fun alpha => Matches received alpha (final alpha) i

/-- Actual selected canonical inverse tables specialize the arbitrary-word
algebra. Q may have been reconstructed earlier; it is not assumed to match R. -/
theorem four_identified_matches (received : Fin 1048576 → QM31Exact)
    (Q : Fin 1024 → QM31Exact) (nodes : Finset QM31Exact)
    (final : QM31Exact → Fin 256 → QM31Exact)
    (identified : ∀ alpha∈nodes, final alpha=coefficientFoldLayer 256 alpha Q)
    (i : Fin 262144) (four : 4≤(matchingNodes received nodes final i).card) :
    FullSlots received Q i := by
  classical
  have inverse := canonical_one_fold_schedule_exact 0
  apply FoldSupportAlgebra.four_folds_identify_slots exactCircleX exactCircleY
    (canonicalOneFoldSchedule 0).circleInv2x
    (canonicalOneFoldSchedule 0).circleInv2y inverse.1 inverse.2
    (exactInitialEncoder Q) received i (matchingNodes received nodes final i) four
  intro alpha member
  have h := Finset.mem_filter.mp member
  have actual := h.2
  change Matches received alpha (final alpha) i at actual
  rw [identified alpha h.1] at actual
  exact (congrFun (selected_fold_commutes Q alpha) i).trans actual

theorem full_slots_matches (received : Fin 1048576 → QM31Exact)
    (Q : Fin 1024 → QM31Exact) (i : Fin 262144) (full : FullSlots received Q i)
    (alpha : QM31Exact) :
    Matches received alpha (coefficientFoldLayer 256 alpha Q) i := by
  have slots : (fun slot => exactInitialEncoder Q (childIndex i slot))=
      (fun slot => received (childIndex i slot)) := funext full
  change exactFinalLinear (coefficientFoldLayer 256 alpha Q) i=_
  rw [← congrFun (selected_fold_commutes Q alpha) i,
    circleFoldLayer_apply,circleFoldLayer_apply,slots]

/-- Multiplicity does not create new geometric agreement: with at least
four coherent branches, four matches are equivalent to full raw support. -/
theorem four_matches_iff_full (received : Fin 1048576 → QM31Exact)
    (Q : Fin 1024 → QM31Exact) (nodes : Finset QM31Exact) (four : 4≤nodes.card)
    (final : QM31Exact → Fin 256 → QM31Exact)
    (identified : ∀ alpha∈nodes, final alpha=coefficientFoldLayer 256 alpha Q)
    (i : Fin 262144) :
    4≤(matchingNodes received nodes final i).card ↔ FullSlots received Q i := by
  classical
  constructor
  · exact four_identified_matches received Q nodes final identified i
  · intro full
    have equal : matchingNodes received nodes final i=nodes := by
      apply Finset.filter_eq_self.mpr
      intro alpha member
      rw [identified alpha member]
      exact full_slots_matches received Q i full alpha
    rw [equal]
    exact four

/-- The complete intersection of all coherent matching sets is the same
full-slot support. In particular, multiplicity closure is not a larger set. -/
theorem all_matches_iff_full (received : Fin 1048576 → QM31Exact)
    (Q : Fin 1024 → QM31Exact) (nodes : Finset QM31Exact) (four : 4≤nodes.card)
    (final : QM31Exact → Fin 256 → QM31Exact)
    (identified : ∀ alpha∈nodes, final alpha=coefficientFoldLayer 256 alpha Q)
    (i : Fin 262144) :
    (∀ alpha∈nodes, Matches received alpha (final alpha) i) ↔ FullSlots received Q i := by
  classical
  constructor
  · intro matchedAt
    apply four_identified_matches received Q nodes final identified i
    have equal : matchingNodes received nodes final i=nodes := Finset.filter_eq_self.mpr matchedAt
    rw [equal]
    exact four
  · intro full alpha member
    rw [identified alpha member]
    exact full_slots_matches received Q i full alpha

/-- A finite union of exposed supports, censored by fourfold observation
multiplicity. No complete per-branch matching set is supplied or enumerated. -/
def observedClosure (nodes : Finset QM31Exact)
    (observed : QM31Exact → Finset (Fin 262144)) : Finset (Fin 262144) := by
  classical
  exact (nodes.biUnion observed).filter fun i => 4≤(nodes.filter fun alpha => i∈observed alpha).card

/-- Different branches can expose different supports. Four certified matches
at each retained fibre suffice; no one observed support common to all is used. -/
theorem observed_closure_full (received : Fin 1048576 → QM31Exact)
    (Q : Fin 1024 → QM31Exact) (nodes : Finset QM31Exact)
    (final : QM31Exact → Fin 256 → QM31Exact)
    (identified : ∀ alpha∈nodes, final alpha=coefficientFoldLayer 256 alpha Q)
    (observed : QM31Exact → Finset (Fin 262144))
    (valid : ∀ alpha∈nodes, ∀ i∈observed alpha, Matches received alpha (final alpha) i) :
    ∀ i∈observedClosure nodes observed, FullSlots received Q i := by
  classical
  intro i member
  have many := (Finset.mem_filter.mp member).2
  apply four_identified_matches received Q nodes final identified i
  apply many.trans
  apply Finset.card_le_card
  intro alpha present
  have h := Finset.mem_filter.mp present
  exact Finset.mem_filter.mpr ⟨h.1,valid alpha h.1 i h.2⟩

/-- An adaptive next final is identified through its explicit overlap with
the certified closure, not through a presumed all-branches common support. -/
theorem closure_overlap_identifies (received : Fin 1048576 → QM31Exact)
    (Q : Fin 1024 → QM31Exact) (nodes : Finset QM31Exact)
    (final : QM31Exact → Fin 256 → QM31Exact)
    (identified : ∀ alpha∈nodes, final alpha=coefficientFoldLayer 256 alpha Q)
    (observed : QM31Exact → Finset (Fin 262144))
    (valid : ∀ alpha∈nodes, ∀ i∈observed alpha, Matches received alpha (final alpha) i)
    (alpha : QM31Exact) (nextFinal : Fin 256 → QM31Exact)
    (nextObserved : Finset (Fin 262144))
    (nextValid : ∀ i∈nextObserved, Matches received alpha nextFinal i)
    (large : 255<(observedClosure nodes observed ∩ nextObserved).card) :
    nextFinal=coefficientFoldLayer 256 alpha Q := by
  apply common_support_identifies received (observedClosure nodes observed ∩ nextObserved)
    large Q
  · intro i member
    exact observed_closure_full received Q nodes final identified observed valid i
      (Finset.mem_inter.mp member).1
  · intro i member
    exact nextValid i (Finset.mem_inter.mp member).2

#print axioms four_identified_matches
#print axioms full_slots_matches
#print axioms four_matches_iff_full
#print axioms all_matches_iff_full
#print axioms observed_closure_full
#print axioms closure_overlap_identifies
end
end AspisV8.FoldSupportClosure
