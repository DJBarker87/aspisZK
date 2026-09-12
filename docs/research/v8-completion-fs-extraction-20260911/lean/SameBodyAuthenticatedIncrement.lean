import SameBodyOpenedQueryUpdate

/-!
# Authenticated same-body q22 increment

This leaf runs the existing selected wire/record/inverse/Merkle pipeline and
constructs the shifted q22 increment and its canonical 16 transcript bytes.
Pipeline failure remains a named aggregate `none`; the successful branch's
existing `run_checks` theorem exposes all four internal checks.  The scalar
is exactly the `SameBodyRelation.increment` input at the same final, schedule
and rho.  Authentication against the chronological C1/C2 prefixes remains the
existing explicit failure alternative; opening equality is not assumed.

This is the strongest direct deterministic bridge presently available.  The
live `List Nat` schedule still needs to be converted using its sampler-success
certificate, and the chronological prefixes/log must be constructed by the
whole execution before this can replace `IncrementProducer` in the live
script.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.SameBodyAuthenticatedIncrement

open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV5ComponentCQM31TowerExact AspisV5ComponentCQM31Representation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.AuthenticatedPhaseWords
open AspisV8.SelectedWireBytes AspisV8.SelectedWireMerkleRun
open AspisV8.SelectedMultiproofOpeningEquality
open AspisV8.SameBodyAuthenticatedSlots AspisV8.SameBodyOpenedRun
open AspisV8.SameBodyOpenedQueryUpdate
open AspisV8.OODInterpolant AspisV8.PostQueryFunctional
open AspisV8Completion.SameBodyQueryClaim AspisV8Completion.SameBodyQueryClaimExact
open AspisV8Completion.SameBodyRelation
open scoped BigOperators

abbrev Bytes := List UInt8
abbrev K := QM31Exact
abbrev Position := Fin 262144
abbrev Query := Fin 22 -> Position
abbrev OldByte := AspisPool.V7MerkleQueryGrammar.Byte

noncomputable section

def wireBytes (bytes : Bytes) : List OldByte := bytes.map UInt8.toFin

inductive Error where
  /-- The existing functional `run` retains the precise internal short-circuit
  order; this wrapper does not misclassify its `none` without another replay. -/
  | openedPipeline
  deriving DecidableEq

/-- A success value contains proofs made by the actual functional pipeline,
not a separately supplied opening-equality certificate. -/
structure Prepared (view : RawHashInput -> Digest208) where
  body : Bytes
  query : Query
  data : Data (K := K)
  alpha : K
  rho : K
  result : Output
  runSuccess : AspisV8.SameBodyOpenedRun.run view
    (wireBytes body) query data = some result

/-- The selected functional pipeline constructs the result.  Its existing
`run_checks` theorem exposes wire, record, inverse and Merkle success on the
successful branch.  `none` stays a named aggregate pipeline failure rather
than being guessed into one of those classes after the fact. -/
def prepare (view : RawHashInput -> Digest208) (body : Bytes)
    (query : Query) (data : Data (K := K)) (alpha rho : K) :
    Except Error (Prepared view) :=
  match h : AspisV8.SameBodyOpenedRun.run view (wireBytes body) query data with
  | none => .error .openedPipeline
  | some result => .ok {
      body := body
      query := query
      data := data
      alpha := alpha
      rho := rho
      result := result
      runSuccess := h }

def Prepared.opened {view : RawHashInput -> Digest208}
    (prepared : Prepared view) : Fin 22 -> K :=
  AspisV8.SameBodyOpenedRun.opened prepared.result prepared.data
    prepared.query prepared.alpha

/-- Literal source `rho, rho^2, ..., rho^22` dot opened values. -/
def Prepared.scalar {view : RawHashInput -> Digest208}
    (prepared : Prepared view) : K :=
  SameBodyQueryClaim.increment (ringArithmetic (1/4 : K))
    prepared.rho prepared.opened

/-- The exact function shape consumed by `SameBodyRelation.consume`.  Only
its application to the same final/schedule/rho is claimed below. -/
def Prepared.relationIncrement {view : RawHashInput -> Digest208}
    (prepared : Prepared view) :
    Final K -> Query -> K -> K :=
  fun _ query rho => SameBodyQueryClaim.increment (ringArithmetic (1/4 : K))
    rho (AspisV8.SameBodyOpenedRun.opened prepared.result prepared.data
      query prepared.alpha)

def canonicalBytes (value : K) : Bytes :=
  (List.ofFn (encodeQM31ExactLE value)).map UInt8.ofFin

def Prepared.bytes {view : RawHashInput -> Digest208}
    (prepared : Prepared view) : Bytes := canonicalBytes prepared.scalar

theorem canonicalBytes_length (value : K) : (canonicalBytes value).length = 16 := by
  simp [canonicalBytes]

theorem canonicalBytes_old (value : K) :
    wireBytes (canonicalBytes value) =
      List.ofFn (encodeQM31ExactLE value) := by
  simp [canonicalBytes, wireBytes, List.map_map, Function.comp_def]

def canonicalField (value : K) : QM31Bytes :=
  encodeQM31ExactLE value

theorem canonicalField_eq (value : K) :
    canonicalField value = encodeQM31ExactLE value := by
  rfl

theorem canonicalBytes_decode (value : K) :
    decodeQM31ExactLE (canonicalField value) = some value := by
  rw [canonicalField_eq, decodeQM31ExactLE_encodeQM31ExactLE]

theorem relation_increment_exact {view : RawHashInput -> Digest208}
    (prepared : Prepared view) (final : Final K) :
    prepared.relationIncrement final prepared.query prepared.rho = prepared.scalar := by
  rfl

/-- Authentication is not presumed.  Outside the already defined
authentication failure, the constructed scalar is the exact shifted dot of
the actual prefix-bound folded quotient values at this schedule. -/
theorem authenticated_scalar_or_failure {view : RawHashInput -> Digest208}
    (prepared : Prepared view)
    (c1Prefix c2Prefix : AnswerPrefix) (fullLog : OrderedRawQueryLog)
    (c1Answers : ∀ record ∈ c1Prefix, view record.1 = record.2)
    (c2Answers : ∀ record ∈ c2Prefix, view record.1 = record.2)
    (c1Included : TraceIncludedInLog (rawPrefix c1Prefix) fullLog)
    (c2Included : TraceIncludedInLog (rawPrefix c2Prefix) fullLog)
    (callsIncluded : TraceIncludedInLog
      (AspisV8.MinimalMultiproofPaths.leafLog prepared.query
        (wireRecords prepared.result.wire) ++ prepared.result.trace) fullLog) :
    AuthenticationFailure view c1Prefix c2Prefix
        (wireRoots prepared.result.wire) fullLog prepared.query \/
    prepared.scalar =
      ∑ i : Fin 22, prepared.rho^(i.val+1) *
        (AspisV8.SelectedReceivedOracle.oracle (0 : Fin 1024 -> K)
          (AspisV8.SelectedQuotientOriginal.virtual prepared.data
            (prefixBatch c1Prefix c2Prefix prepared.result.wire
              prepared.data.gamma))).folded prepared.alpha
                (storedPoint (K := K) (prepared.query i)) := by
  rcases run_authenticated_opened_or_failure view
      (wireBytes prepared.body) prepared.query prepared.data
      prepared.result prepared.runSuccess c1Prefix c2Prefix fullLog c1Answers
      c2Answers c1Included c2Included callsIncluded prepared.alpha with bad | good
  · exact Or.inl bad
  · apply Or.inr
    rw [Prepared.scalar, increment_exact]
    apply Finset.sum_congr rfl
    intro i _
    rw [Prepared.opened, good i]

#print axioms canonicalBytes_old
#print axioms canonicalBytes_decode
#print axioms relation_increment_exact
#print axioms authenticated_scalar_or_failure

end
end AspisV8Completion.SameBodyAuthenticatedIncrement
