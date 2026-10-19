import GSRootCandidateContract
import RRFinalMessageRecovery

set_option autoImplicit false

namespace AspisWide.GSFinalMessageCandidateFilter

open CompPoly Polynomial AspisWide.GSRootCandidateContract
open AspisR1.RRFinalMessageRecovery
open AspisV5FriConcreteEncoderApplicability

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [LawfulBEq (CPolynomial K)]

def filterCandidates (candidates : List (List K)) : List (Fin 256 → K) :=
  candidates.filterMap fun cs =>
    filterFinal (CPolynomial.ofArray cs.toArray)

theorem filterCandidates_mem_iff
    (Q : (K[X])[X]) (candidates : List (List K))
    (hc : Candidates Q 256 candidates) (m : Fin 256 → K) :
    m ∈ filterCandidates candidates ↔ Q.eval (encodeFinal m).toPoly = 0 := by
  constructor
  · intro hm
    obtain ⟨cs, hcs, hfilter⟩ := List.mem_filterMap.mp hm
    have he := filterFinal_sound (CPolynomial.ofArray cs.toArray) m hfilter
    have hp : toPolynomial cs = (encodeFinal m).toPoly := by
      rw [← ofArray_toPolynomial, he]
    rw [← hp]
    exact hc.1 cs hcs
  · intro hm
    have hd : (encodeFinal m).toPoly.natDegree < 256 := by
      rw [encodeFinal_toPoly]
      exact lt_of_le_of_lt
        (naturalCoefficientPolynomial_natDegree_le (by omega : 0 < 256) m)
        (by decide)
    obtain ⟨cs, hcs, hp⟩ := hc.2 (encodeFinal m).toPoly hm (Or.inr hd)
    have he : CPolynomial.ofArray cs.toArray = encodeFinal m := by
      apply CPolynomial.ringEquiv.injective
      change (CPolynomial.ofArray cs.toArray).toPoly = (encodeFinal m).toPoly
      rw [ofArray_toPolynomial, hp]
    apply List.mem_filterMap.mpr
    refine ⟨cs, hcs, ?_⟩
    rw [he]
    exact filterFinal_complete m

#print axioms filterCandidates_mem_iff

end AspisWide.GSFinalMessageCandidateFilter
