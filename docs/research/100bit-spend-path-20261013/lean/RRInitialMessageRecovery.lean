import RRConcreteRawRecovery
import InitialMessagePublicFilter

set_option autoImplicit false
namespace AspisR1.RRInitialMessageRecovery
open CompPoly Polynomial RRDenseCoeffVector RRVectorRowPolynomialBridge
open AspisR1.RRConcreteState AspisR1.RRConcreteValidState
open AspisR1.RRConcreteInitialValidStateFromFacts AspisR1.RRConcreteTraversal
open AspisR1.RRConcreteRawRecovery AspisR1.RRProgramRecoveryContracts
open AspisR1.RRFiniteRootSamplerNormalizedStateBridge
open AspisWide.InitialForwardEncoderBaseV9 AspisWide.InitialMessageForwardFilterV3
open AspisWide.InitialMessagePublicFilter AspisV5FriCircleEncoderDistance
open AspisR1.CompPolyFactorMeanTools

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [LawfulBEq (CPolynomial K)]

/-- The same executable public filter is applied to canonical polynomials
constructed from the actual coefficient lists returned by root recovery. -/
def imageFilter (candidates : List (List K)) : List (Fin 1024 → K) :=
  candidates.filterMap fun cs => filterPublic (CPolynomial.ofArray cs.toArray)

theorem imageFilter_mem_iff (s : RawState K) (candidates : List (List K))
    (hc : CandidateResult model 1025 s candidates) (m : Fin 1024 → K) :
    m ∈ imageFilter candidates ↔ (model s).eval (encodeInitialC m).toPoly = 0 := by
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
    obtain ⟨cs, hcs, hp⟩ := hc.2 _ hm (Or.inr hd)
    have he : CPolynomial.ofArray cs.toArray = encodeInitialC m := by
      apply CPolynomial.ringEquiv.injective
      change (CPolynomial.ofArray cs.toArray).toPoly = (encodeInitialC m).toPoly
      rw [ofArray_toPolynomial, hp]
    apply List.mem_filterMap.mpr
    refine ⟨cs, hcs, ?_⟩
    rw [he]
    exact filterPublic_complete m

def recoverMessages (ell q t : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0)
    (H : {i : Nat // i ∈ Finset.range
      (1025 * mass ell (initialValidState ell s hdegree hQ))} → Fin t → K × K) :
    Option (List (Fin 1024 → K)) :=
  (recover ell q t 1025 s hdegree hQ H).1.map imageFilter

theorem recoverMessages_correct (ell q t : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range
      (1025 * mass ell (initialValidState ell s hdegree hQ))} → Fin t → K × K)
    (messages : List (Fin 1024 → K))
    (hs : recoverMessages ell q t s hdegree hQ H = some messages) :
    ∀ m, m ∈ messages ↔ (model s).eval (encodeInitialC m).toPoly = 0 := by
  cases hr : (recover ell q t 1025 s hdegree hQ H).1 with
  | none => simp [recoverMessages, hr] at hs
  | some candidates =>
    have hm : imageFilter candidates = messages := by
      simpa only [recoverMessages, hr, Option.map_some, Option.some.injEq] using hs
    subst messages
    exact imageFilter_mem_iff s candidates
      (recover_correct ell q t 1025 s hdegree hQ hq H candidates hr)

theorem recoverMessages_abort_indicator (ell q t : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0)
    (H : {i : Nat // i ∈ Finset.range
      (1025 * mass ell (initialValidState ell s hdegree hQ))} → Fin t → K × K) :
    abortIndicator (recoverMessages ell q t s hdegree hQ H) =
      abortIndicator (recover ell q t 1025 s hdegree hQ H).1 := by
  cases hr : (recover ell q t 1025 s hdegree hQ H).1 <;>
    simp [recoverMessages, hr, abortIndicator]

#print axioms imageFilter
#print axioms imageFilter_mem_iff
#print axioms recoverMessages
#print axioms recoverMessages_correct
#print axioms recoverMessages_abort_indicator
end AspisR1.RRInitialMessageRecovery
