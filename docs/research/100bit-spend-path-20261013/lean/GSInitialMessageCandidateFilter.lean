import GSRootCandidateContract
import InitialForwardEncoderBaseV9
import InitialMessagePublicFilter

set_option autoImplicit false

namespace AspisWide.GSInitialMessageCandidateFilter

open CompPoly Polynomial RRDenseCoeffVector
open AspisWide.GSRootCandidateContract
open AspisWide.InitialForwardEncoderBaseV9
open AspisWide.InitialMessageForwardFilterV3
open AspisWide.InitialMessagePublicFilter
open AspisV5FriCircleEncoderDistance AspisV5FriConcreteEncoderApplicability

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [LawfulBEq (CPolynomial K)]

/-- The array-backed CompPoly input has the same polynomial model as the
released dense coefficient list. -/
theorem ofArray_toPolynomial (cs : List K) :
    (CPolynomial.ofArray cs.toArray).toPoly = toPolynomial cs := by
  apply Polynomial.ext
  intro n
  rw [CPolynomial.ofArray_toPoly, CPolynomial.Raw.coeff_toPoly]
  rw [coeff_toPolynomial]
  simp [coeffAt]

def filterCandidates (candidates : List (List K)) : List (Fin 1024 → K) :=
  candidates.filterMap fun cs =>
    filterPublic (CPolynomial.ofArray cs.toArray)

theorem filterCandidates_mem_iff
    (Q : (K[X])[X]) (candidates : List (List K))
    (hc : Candidates Q 1025 candidates) (m : Fin 1024 → K) :
    m ∈ filterCandidates candidates ↔ Q.eval (encodeInitialC m).toPoly = 0 := by
  constructor
  · intro hm
    obtain ⟨cs, hcs, hfilter⟩ := List.mem_filterMap.mp hm
    have he := filterPublic_sound (CPolynomial.ofArray cs.toArray) m hfilter
    have hp : toPolynomial cs = (encodeInitialC m).toPoly := by
      rw [← ofArray_toPolynomial, he]
    rw [← hp]
    exact hc.1 cs hcs
  · intro hm
    have hd : (encodeInitialC m).toPoly.natDegree < 1025 := by
      rw [encodeInitialC_toPoly]
      exact lt_of_le_of_lt (circleNumerator_natDegree_le _ _) (by decide)
    obtain ⟨cs, hcs, hp⟩ := hc.2 (encodeInitialC m).toPoly hm (Or.inr hd)
    have he : CPolynomial.ofArray cs.toArray = encodeInitialC m := by
      apply CPolynomial.ringEquiv.injective
      change (CPolynomial.ofArray cs.toArray).toPoly = (encodeInitialC m).toPoly
      rw [ofArray_toPolynomial, hp]
    apply List.mem_filterMap.mpr
    refine ⟨cs, hcs, ?_⟩
    rw [he]
    exact filterPublic_complete m

#print axioms ofArray_toPolynomial
#print axioms filterCandidates_mem_iff

end AspisWide.GSInitialMessageCandidateFilter
