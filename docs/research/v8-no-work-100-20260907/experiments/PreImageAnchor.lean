import PartialFoldRecovery

/-! Geometry-only pre-image-challenge anchor. Eligibility uses the fixed
received word and existence of close final codewords, never transcript
responses, provider membership or the image challenge. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.PreImageAnchor

open Finset
open AspisV8.PartialFoldRecovery
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriCoherentCandidateExtraction

noncomputable section
variable {K F : Type*} [Field K] [DecidableEq K] [Field F] [Algebra F K]

/-- A fixed 4B-close full quotient represents every B-close final if the
two final codewords would otherwise exceed their literal overlap cap. -/
theorem close_final_identifies_fold {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (cap B : Nat)
    (overlap : ∀ left right : Fin n → K, left ≠ right →
      (agreementSet (encoder left) (encoder right)).card ≤ cap)
    (margin : 5*B+cap < m)
    (received : Fin (4*m) → K) (anchor : Fin (4*n) → K)
    (anchorClose : (fibreBad (circleLiftEncoder encoder x y anchor) received).card ≤ 4*B)
    (alpha : K) (final : Fin n → K)
    (finalClose : (foldedBad encoder inverse2x inverse2y received alpha final).card ≤ B) :
    final = coefficientFoldLayer n alpha anchor := by
  classical
  by_contra different
  let anchorBad := fibreBad (circleLiftEncoder encoder x y anchor) received
  let finalBad := foldedBad encoder inverse2x inverse2y received alpha final
  let bad := anchorBad ∪ finalBad
  let good := Finset.univ \ bad
  change anchorBad.card ≤ 4*B at anchorClose
  change finalBad.card ≤ B at finalClose
  have badBound : bad.card ≤ 5*B := by
    have unionBound : bad.card ≤ anchorBad.card + finalBad.card :=
      Finset.card_union_le anchorBad finalBad
    omega
  have total : good.card + bad.card = m := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
    simpa only [good, Finset.card_univ, Fintype.card_fin] using h
  have commutes : circleFoldLayer m alpha inverse2x inverse2y
        (circleLiftEncoder encoder x y anchor) =
      encoder (coefficientFoldLayer n alpha anchor) := by
    have h := congrArg (fun f : (Fin (4*n) → K) →ₗ[K] (Fin m → K) => f anchor)
      (circleFoldLayer_circleLiftEncoder encoder alpha x y inverse2x inverse2y hx hy)
    simpa only [LinearMap.comp_apply] using h
  have included : good ⊆ agreementSet (encoder final)
      (encoder (coefficientFoldLayer n alpha anchor)) := by
    intro i hi
    have outside := (Finset.mem_sdiff.mp hi).2
    have noAnchor : i ∉ anchorBad := fun h => outside (Finset.mem_union_left _ h)
    have noFinal : i ∉ finalBad := fun h => outside (Finset.mem_union_right _ h)
    have receivedSlots : (fun slot => circleLiftEncoder encoder x y anchor (childIndex i slot)) =
        (fun slot => received (childIndex i slot)) := by
      funext slot
      by_contra wrong
      apply noAnchor
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨slot, wrong⟩⟩
    have folds : circleFoldLayer m alpha inverse2x inverse2y
          (circleLiftEncoder encoder x y anchor) i =
        circleFoldLayer m alpha inverse2x inverse2y received i := by
      rw [circleFoldLayer_apply, circleFoldLayer_apply, receivedSlots]
    have finalAt : encoder final i = circleFoldLayer m alpha inverse2x inverse2y received i := by
      by_contra wrong
      apply noFinal
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, wrong⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    exact finalAt.trans (folds.symm.trans (congrFun commutes i))
  have goodCap := (Finset.card_le_card included).trans
    (overlap final (coefficientFoldLayer n alpha anchor) different)
  omega

/-- The dense branch constructs its own anchor from the received-word
geometry. The existential anchor precedes every alpha/final quantifier.
No tau, relation response, provider outcome or acceptance flag is an input. -/
theorem geometric_anchor_dichotomy {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (cap B : Nat)
    (overlap : ∀ left right : Fin n → K, left ≠ right →
      (agreementSet (encoder left) (encoder right)).card ≤ cap)
    (margin : 5*B+cap < m)
    (received : Fin (4*m) → K) (challenges : Finset K) :
    (closeFoldChallenges encoder inverse2x inverse2y received B challenges).card ≤ 3 ∨
      ∃ anchor : Fin (4*n) → K,
        (fibreBad (circleLiftEncoder encoder x y anchor) received).card ≤ 4*B ∧
        ∀ alpha : K, ∀ final : Fin n → K,
          (foldedBad encoder inverse2x inverse2y received alpha final).card ≤ B →
          final = coefficientFoldLayer n alpha anchor := by
  classical
  by_cases sparse : (closeFoldChallenges encoder inverse2x inverse2y received B challenges).card ≤ 3
  · exact Or.inl sparse
  · right
    have existsAnchor : ∃ anchor : Fin (4*n) → K,
        (fibreBad (circleLiftEncoder encoder x y anchor) received).card ≤ 4*B := by
      by_contra missing
      have far (anchor : Fin (4*n) → K) :
          4*B < (fibreBad (circleLiftEncoder encoder x y anchor) received).card := by
        by_contra notFar
        exact missing ⟨anchor, by omega⟩
      exact sparse (far_close_fold_challenges_le_three encoder x y inverse2x inverse2y
        hx hy received B challenges far)
    obtain ⟨anchor, anchorClose⟩ := existsAnchor
    refine ⟨anchor, anchorClose, ?_⟩
    intro alpha final finalClose
    exact close_final_identifies_fold encoder x y inverse2x inverse2y hx hy cap B overlap
      margin received anchor anchorClose alpha final finalClose

#print axioms close_final_identifies_fold
#print axioms geometric_anchor_dichotomy

end
end AspisV8.PreImageAnchor
