import GSRootCandidateContract
import GSActualEncoderGRSBridge
import RRFinalMessageRecovery

set_option autoImplicit false

namespace AspisWide.GSFinalMessageCandidateFilter

open CompPoly Polynomial RRDenseCoeffVector AspisWide.GSRootCandidateContract
open AspisWideTower
open AspisWide.GSActualEncoderGRSBridge
open AspisR1.RRFinalMessageRecovery
open AspisR1.RRFiniteRootSamplerNormalizedStateBridge
open AspisV5FriConcreteEncoderApplicability

variable [BEq WideExact] [LawfulBEq WideExact] [DecidableEq WideExact]
  [NeZero (2 : WideExact)] [Algebra (ZMod AspisCircleGroupOrder.P) WideExact]
  [Fintype WideExact] [LawfulBEq (CPolynomial WideExact)]

def filterCandidates (candidates : List (List WideExact)) : List (Fin 256 → WideExact) :=
  candidates.filterMap fun cs =>
    filterFinal (CPolynomial.ofArray cs.toArray)

theorem filterCandidates_mem_iff
    (Q : (WideExact[X])[X]) (candidates : List (List WideExact))
    (hc : Candidates Q 256 candidates) (m : Fin 256 → WideExact) :
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
    have hd : (encodeFinal m).toPoly.natDegree < 256 :=
      final_encode_degree_lt m
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
