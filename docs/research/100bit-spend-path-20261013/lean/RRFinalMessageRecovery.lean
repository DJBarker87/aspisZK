import RRConcreteRawRecovery
import WideExactNaturalBasisTriangularV14
import InitialForwardEncoderBaseV9

set_option autoImplicit false
namespace AspisR1.RRFinalMessageRecovery
open CompPoly Polynomial RRDenseCoeffVector RRVectorRowPolynomialBridge
open AspisR1.RRConcreteState AspisR1.RRConcreteValidState
open AspisR1.RRConcreteInitialValidStateFromFacts AspisR1.RRConcreteTraversal
open AspisR1.RRConcreteRawRecovery AspisR1.RRProgramRecoveryContracts
open AspisR1.RRFiniteRootSamplerNormalizedStateBridge
open AspisWide.InitialForwardEncoderBaseV9
open AspisV5FriConcreteEncoderApplicability AspisV5FriConcreteEncoderCommutation
open AspisR1.CompPolyFactorMeanTools

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [LawfulBEq (CPolynomial K)]

private theorem triangular_encode_eq : ∀ n (c : Fin (n + 1) → K),
    AspisWide.NaturalBasisTriangularV4.encode n c = encodeBasis n c := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    rw [AspisWide.NaturalBasisTriangularV4.encode, encodeBasis, ih]
    rfl

def encodeFinal (m : Fin 256 → K) : CPolynomial K :=
  AspisWide.NaturalBasisTriangularV4.encode 255 m

def decodeFinal (q : CPolynomial K) : Fin 256 → K :=
  AspisWide.NaturalBasisTriangularV4.decode 255 q

theorem encodeFinal_toPoly (m : Fin 256 → K) :
    (encodeFinal m).toPoly = naturalCoefficientPolynomial m := by
  rw [encodeFinal, triangular_encode_eq, encodeBasis_toPoly_basisSum]
  exact (naturalCoefficientPolynomial_eq_basisSum (K := K) (n := 256)
    (by omega) m).symm

theorem decodeFinal_encodeFinal (m : Fin 256 → K) :
    decodeFinal (encodeFinal m) = m :=
  AspisWide.NaturalBasisTriangularV4.decode_encode 255 m

def filterFinal (q : CPolynomial K) : Option (Fin 256 → K) :=
  let m := decodeFinal q
  if encodeFinal m == q then some m else none

theorem filterFinal_sound (q : CPolynomial K) (m : Fin 256 → K)
    (h : filterFinal q = some m) : encodeFinal m = q := by
  simp only [filterFinal] at h
  split at h
  · rename_i he
    injection h with hm
    rw [← hm]
    exact LawfulBEq.eq_of_beq he
  · simp at h

theorem filterFinal_complete (m : Fin 256 → K) :
    filterFinal (encodeFinal m) = some m := by
  simp [filterFinal, decodeFinal_encodeFinal]

def imageFilter (candidates : List (List K)) : List (Fin 256 → K) :=
  candidates.filterMap fun cs => filterFinal (CPolynomial.ofArray cs.toArray)

theorem imageFilter_mem_iff (s : RawState K) (candidates : List (List K))
    (hc : CandidateResult model 256 s candidates) (m : Fin 256 → K) :
    m ∈ imageFilter candidates ↔ (model s).eval (encodeFinal m).toPoly = 0 := by
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
    obtain ⟨cs, hcs, hp⟩ := hc.2 _ hm (Or.inr hd)
    have he : CPolynomial.ofArray cs.toArray = encodeFinal m := by
      apply CPolynomial.ringEquiv.injective
      change (CPolynomial.ofArray cs.toArray).toPoly = (encodeFinal m).toPoly
      rw [ofArray_toPolynomial, hp]
    apply List.mem_filterMap.mpr
    refine ⟨cs, hcs, ?_⟩
    rw [he]
    exact filterFinal_complete m

def recoverMessages (ell q t : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0)
    (H : {i : Nat // i ∈ Finset.range
      (256 * mass ell (initialValidState ell s hdegree hQ))} → Fin t → K × K) :
    Option (List (Fin 256 → K)) :=
  (recover ell q t 256 s hdegree hQ H).1.map imageFilter

theorem recoverMessages_correct (ell q t : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range
      (256 * mass ell (initialValidState ell s hdegree hQ))} → Fin t → K × K)
    (messages : List (Fin 256 → K))
    (hs : recoverMessages ell q t s hdegree hQ H = some messages) :
    ∀ m, m ∈ messages ↔ (model s).eval (encodeFinal m).toPoly = 0 := by
  cases hr : (recover ell q t 256 s hdegree hQ H).1 with
  | none => simp [recoverMessages, hr] at hs
  | some candidates =>
    have hm : imageFilter candidates = messages := by
      simpa only [recoverMessages, hr, Option.map_some, Option.some.injEq] using hs
    subst messages
    exact imageFilter_mem_iff s candidates
      (recover_correct ell q t 256 s hdegree hQ hq H candidates hr)

theorem recoverMessages_abort_indicator (ell q t : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0)
    (H : {i : Nat // i ∈ Finset.range
      (256 * mass ell (initialValidState ell s hdegree hQ))} → Fin t → K × K) :
    abortIndicator (recoverMessages ell q t s hdegree hQ H) =
      abortIndicator (recover ell q t 256 s hdegree hQ H).1 := by
  cases hr : (recover ell q t 256 s hdegree hQ H).1 <;>
    simp [recoverMessages, hr, abortIndicator]

#print axioms encodeFinal_toPoly
#print axioms decodeFinal_encodeFinal
#print axioms filterFinal_sound
#print axioms filterFinal_complete
#print axioms imageFilter_mem_iff
#print axioms recoverMessages
#print axioms recoverMessages_correct
#print axioms recoverMessages_abort_indicator
end AspisR1.RRFinalMessageRecovery
