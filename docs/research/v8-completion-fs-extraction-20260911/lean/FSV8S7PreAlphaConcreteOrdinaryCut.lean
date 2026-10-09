import FSV8S7SelectedSourcePrefixBudget
import FSV8S7CompactWordTargetInclusion
import SameBodyChronologicalRelationTerminal

/-!
# Concrete pre-alpha ordinary cut from one selected source execution

This leaf makes the part of the ordinary polynomial that is genuinely
available before the alpha0 sampler explicit.  In particular, it does not
receive a `z`, gamma, kappa, ordinary claim, response0, or compact polynomial
from a caller.  They are projected from a successful run of the selected
same-body prefix and its one canonical parse.

It intentionally stops short of an ordinary *bad-event* inclusion.  That
requires a source-produced reference word/covector family (the `chunks` in
`FSV8S7CompactWordTargetInclusion`) and a relation-discrepancy implication.
Neither is a field of the selected prefix result, so treating either as a
definition of this cut would reintroduce the S7 caller-supplied-target gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000

namespace AspisV8Completion.FSV8S7PreAlphaConcreteOrdinaryCut

open FSOracleExecution FSBoundedTranscript
open FSLiveSemanticPrefix
open FSV8S7SelectedSourcePrefixBudget
open FSV8S5SelectedVerifierCallbacks
open FSV8S5CompactPolynomialTarget
open FSV8S7CompactWordTargetInclusion
open SameBodyFunctionalProducerSource
open SameBodyRelation

noncomputable section

abbrev Bytes := List UInt8
abbrev K := FSNonzeroQM31.K
abbrev Wire := SameBodySemanticWire.Wire

/-- The exact round-zero relation message parsed from the canonical fixed
field word.  This is the same six field positions whose byte slice is absorbed
under relation label 52 by the selected prefix. -/
def response0OfWire (wire : Wire) : Sent K :=
  response (FSLiveSemanticPrefix.wordOfValues wire.values) 0

/-- All scalar inputs of the compact initial relation polynomial that the
selected source has fixed immediately before the alpha0 nonce/sampler. -/
structure Cut (body : Bytes) where
  wire : Wire
  parsed : SameBodySemanticWire.parse body = some wire
  semantic : FSLiveSemanticPrefix.Success
  out : FSV7OODBodyScript.Result
  gamma : K
  kappa : K
  tau : K
  functional : Encoded
  functionalRunExact : fromInputs out gamma kappa body semantic.z = some functional
  response0 : Sent K
  response0Exact : response0 = response0OfWire wire

/-- The actual source claim, not a separate caller field. -/
def Cut.claim {body : Bytes} (cut : Cut body) : K := cut.functional.value.claim

/-- The concrete compact coefficient vector fixed by a pre-alpha cut. -/
def Cut.compact {body : Bytes} (cut : Cut body) : Coeff7 K :=
  SameBodyRelation.compact
    (SameBodyQueryClaimExact.ringArithmetic (1 / 4 : K)).toArithmetic
    cut.claim cut.response0

/-- Construct the cut from a successful run of the selected source prefix.
All fields come either from its dependent result or from the one parse which
that successful run itself entails. -/
def ofPrefix {body : Bytes} (wire : Wire)
    (parsed : SameBodySemanticWire.parse body = some wire)
    (pre : BeforeMarkerSuccess body) : Cut body :=
  { wire := wire
    parsed := parsed
    semantic := pre.semantic
    out := pre.before.out
    gamma := pre.before.gamma
    kappa := pre.before.boundary.kappa
    tau := pre.before.boundary.tau
    functional := pre.before.boundary.functional
    functionalRunExact := pre.before.boundary.functionalRun
    response0 := response0OfWire wire
    response0Exact := rfl }

/-- The cut's compact vector is definitionally the source compact relation
polynomial input: source functional claim plus canonical same-body response0.
-/
theorem ofPrefix_compact_exact {body : Bytes} (wire : Wire)
    (parsed : SameBodySemanticWire.parse body = some wire)
    (pre : BeforeMarkerSuccess body) :
    (ofPrefix wire parsed pre).compact =
      SameBodyRelation.compact
        (SameBodyQueryClaimExact.ringArithmetic (1 / 4 : K)).toArithmetic
        pre.before.boundary.functional.value.claim
        (response0OfWire wire) := rfl

/-- A successful selected prefix constructs a concrete pre-alpha ordinary cut
with the source `fromInputs` provenance and the canonical same-body parse.
This is an existential consequence of execution, not an extra root input. -/
theorem successful_prefix_constructs_cut
    (positiveTransfer : Bool) (binding : Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) (oracle : FSBoundedTranscript.Oracle)
    (pre : BeforeMarkerSuccess body) (digest : FSBoundedTranscript.Block)
    (success :
      (run tape (selectedRelaxedThroughBeforeMarkerScript positiveTransfer binding body)
        oracle).1 = some (Except.ok pre, digest)) :
    ∃ cut : Cut body,
      fromInputs cut.out cut.gamma cut.kappa body cut.semantic.z = some cut.functional ∧
      cut.response0 = response0OfWire cut.wire := by
  obtain ⟨wire, parsed, _⟩ :=
    successful_before_marker_has_canonical_body positiveTransfer binding body
      tape oracle pre digest success
  let cut := ofPrefix wire parsed pre
  refine ⟨cut, ?_, ?_⟩
  · exact cut.functionalRunExact
  · exact cut.response0Exact

/-- Exact consumer seam: once a separately constructed source reference
family has supplied the actual word/covector chunks, the target passed to the
degree-six theorem contains the concrete compact coefficients of this cut.
The reference family is deliberately an explicit argument here: this theorem
does not turn an unconstructed received-word/covector relation into one. -/
theorem cut_false_claim_collision_mem_target
    {body : Bytes} {count : Nat} (cut : Cut body)
    (references : Fin count -> Coeff7 K) (index : Fin count)
    (chunks : List (FSV8S5WordCovectorPolynomial.Quad K ×
      FSV8S5WordCovectorPolynomial.Quad K))
    (referenceExact : references index =
      FSV8S5WordCovectorPolynomial.wordCoefficients (1 / 4 : K) chunks)
    (falseClaim : cut.claim ≠ FSV8S5WordCovectorPolynomial.wordDot chunks)
    (alpha : K)
    (collision :
      (poly7 cut.compact).eval alpha =
        (poly7 (FSV8S5WordCovectorPolynomial.wordCoefficients (1 / 4 : K)
          chunks)).eval alpha) :
    alpha ∈
      (CompactTargetData.mk (1 / 4 : K) cut.claim cut.response0 references).target := by
  apply false_claim_collision_mem_compactTarget
  · rw [mul_comm]
    exact SameBodyChronologicalRelationTerminal.quarter_exact
  · exact referenceExact
  · exact falseClaim
  · simpa [CompactTargetData.claimed, Cut.compact] using collision

#print axioms ofPrefix_compact_exact
#print axioms successful_prefix_constructs_cut
#print axioms cut_false_claim_collision_mem_target

end
end AspisV8Completion.FSV8S7PreAlphaConcreteOrdinaryCut
