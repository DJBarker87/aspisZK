import FSLiveSemanticPrefix
import FSV8S5SelectedVerifierCallbacks

/-!
# Selected guard-relaxed prefix through alpha0: syntax-derived resource bounds

This file composes the checked same-body semantic-round script with the
selected read-only-OOD suffix.  In particular, `z` and the digest used by the
suffix are obtained from the semantic result; they are not caller-supplied.
`semanticScript` does not execute the selected payment terminal.  Therefore
this is a pure-rejection overapproximation of the intended source prefix, and
becomes a source bound only after a separate accepted-source-to-relaxed-run
inclusion/effect theorem.

The resulting `3262` bound is the conservative Script-syntax fallback.  It is
not the sharper, source-operation count of 420, a literal-Rust bound, or a
whole-verifier bound.  It covers this guard-relaxed transcript model from
`Transcript::new` through the first relation challenge `alpha0`, on success
and every retained rejection path.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8S7SelectedSourcePrefixBudget

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSLiveSemanticPrefix FSV8S5SelectedVerifierCallbacks
open FSV8BeforeAlphaMarkerFactorization

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K

noncomputable section

/-- Exact source slice absorbed under label 49 after the semantic rounds in
this guard-relaxed model.  In Rust the selected terminal guard occurs before
this absorb.  The wire has already been canonically parsed by `semanticScript`.
-/
def pointClaimBytes (body : Bytes) : Bytes :=
  (body.drop (271 * 16)).take (87 * 16)

inductive Error where
  | semantic (error : FSLiveSemanticPrefix.Error)
  | beforeMarker (error : SelectedPrefixError)
  | marker (error : FSLiveSourceFunctionalMiddle.Error)
  | alpha (error : FSNonzeroQM31.Error)

/-- Values produced by one chronological execution through response0.  The
dependent type of `before` records that the suffix used the `z` returned by
this very semantic run and the same submitted body.
-/
structure BeforeMarkerSuccess (body : Bytes) where
  semantic : FSLiveSemanticPrefix.Success
  before : SelectedBeforeMarker body semantic.z

abbrev BeforeMarkerResult (body : Bytes) :=
  Except Error (BeforeMarkerSuccess body) × Block

/-- Values produced by one chronological execution through alpha0. -/
structure Success (body : Bytes) where
  sourcePrefix : BeforeMarkerSuccess body
  alpha : K
  finalDigest : Block

abbrev Result (body : Bytes) := Except Error (Success body) × Block

/-- Conservative guard-relaxed, source-shaped transcript prefix:

* 1800: canonical parsing and semantic transcript;
* 1: the 87 point-claim absorb;
* 1394: selected OOD/gamma/functional prefix through response0;
* 1: alpha nonce marker;
* 66: ordinary alpha0 candidate.

No query is inserted for padding: `bind`/`pad` only widen the static index.
-/
def selectedRelaxedThroughBeforeMarkerScript (positiveTransfer : Bool)
    (binding : Binding) (body : Bytes) :
    Script Bytes Block (BeforeMarkerResult body) 3195 :=
  bind (m := 1395) (semanticScript positiveTransfer binding body) fun semanticResult =>
    match semanticResult with
    | .error error => .done (.error (.semantic error), zeroDigest)
    | .ok semantic =>
      bind (m := 1394)
          (absorbScript semantic.finalDigest 49 (pointClaimBytes body)) fun afterPoints =>
        map (fun selectedResult =>
          (match selectedResult.1 with
            | .error error => Except.error (.beforeMarker error)
            | .ok before => Except.ok { semantic := semantic, before := before },
            selectedResult.2))
          (selectedBeforeMarkerScript body semantic.z afterPoints)

def selectedRelaxedThroughAlphaScript (positiveTransfer : Bool)
    (binding : Binding) (body : Bytes) :
    Script Bytes Block (Result body) 3262 :=
  bind (m := 67)
      (selectedRelaxedThroughBeforeMarkerScript positiveTransfer binding body) fun prefixResult =>
    match prefixResult.1 with
    | .error error => .done (.error error, prefixResult.2)
    | .ok prefixValue =>
      bind (m := 66)
          (alphaMarkerContinuation prefixValue.before.out prefixValue.before.gamma body
            prefixValue.semantic.z prefixValue.before.boundary) fun markerResult =>
        match markerResult.1 with
        | .error error => .done (.error (.marker error), markerResult.2)
        | .ok _ =>
          map (fun alphaResult =>
            (match alphaResult.1 with
              | .error error => Except.error (.alpha error)
              | .ok alpha => Except.ok
                  { sourcePrefix := prefixValue
                    alpha := alpha
                    finalDigest := alphaResult.2 },
              alphaResult.2))
            (FSNonzeroQM31.candidateScript markerResult.2)

theorem selected_prefix_numeric_budget :
    1800 + 1 + 1394 + 1 + 66 = 3262 := by decide

theorem selected_before_marker_numeric_budget :
    1800 + 1 + 1394 = 3195 := by decide

theorem selectedRelaxedThroughBeforeMarker_call_bound (positiveTransfer : Bool)
    (binding : Binding) (body : Bytes) (tape : FSBoundedTranscript.Tape)
    (oracle : Oracle) :
    (run tape
      (selectedRelaxedThroughBeforeMarkerScript positiveTransfer binding body) oracle).2.log.length
      <= oracle.log.length + 3195 := by
  exact call_bound tape _ _

/-- Calls are derived directly from the selected guard-relaxed syntax. This has
no `priorSourceBound` or `workBudgetBound` premise and applies equally to
cached queries, fresh queries, success, and rejection.
-/
theorem selectedRelaxedThroughAlpha_call_bound (positiveTransfer : Bool)
    (binding : Binding) (body : Bytes) (tape : FSBoundedTranscript.Tape)
    (oracle : Oracle) :
    (run tape (selectedRelaxedThroughAlphaScript positiveTransfer binding body) oracle).2.log.length
      <= oracle.log.length + 3262 := by
  exact call_bound tape _ _

private theorem run_next_le (tape : FSBoundedTranscript.Tape) :
    forall {A : Type} {n : Nat} (script : Script Bytes Block A n)
      (state : State Bytes Block),
      (run tape script state).2.next <= state.next + n := by
  intro A n script
  induction script with
  | done value => intro state; simp [run]
  | abort => intro state; simp [run]
  | @ask remaining input next ih =>
      intro state
      have tail := ih (query tape state input).1 (query tape state input).2
      have step := query_next_bound tape state input
      simp only [run]
      omega

/-- Fresh tape consumption is bounded by the same modeled-call allowance.
Cache hits contribute calls but cannot increase `next`, so no freshness or
independence premise is needed.
-/
theorem selectedRelaxedThroughAlpha_fresh_bound (positiveTransfer : Bool)
    (binding : Binding) (body : Bytes) (tape : FSBoundedTranscript.Tape)
    (oracle : Oracle) :
    (run tape (selectedRelaxedThroughAlphaScript positiveTransfer binding body) oracle).2.next
      <= oracle.next + 3262 := by
  exact run_next_le tape _ _

theorem selectedRelaxedThroughBeforeMarker_fresh_bound (positiveTransfer : Bool)
    (binding : Binding) (body : Bytes) (tape : FSBoundedTranscript.Tape)
    (oracle : Oracle) :
    (run tape
      (selectedRelaxedThroughBeforeMarkerScript positiveTransfer binding body) oracle).2.next
      <= oracle.next + 3195 := by
  exact run_next_le tape _ _

/-- A successful composed prefix exposes the semantic result which fixed the
suffix's `z`.  In particular, the pre-alpha source cannot be paired with a
separately chosen `z`; that equality is enforced by the dependent type of
`sourcePrefix.before`.
-/
theorem successful_output_uses_dynamic_semantic_z (body : Bytes)
    (success : Success body) :
    success.sourcePrefix.before =
      (success.sourcePrefix.before :
        SelectedBeforeMarker body success.sourcePrefix.semantic.z) := rfl

private theorem successful_before_marker_projects_semantic_run
    (positiveTransfer : Bool) (binding : Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) (oracle : Oracle)
    (success : BeforeMarkerSuccess body) (returnedDigest : Block)
    (accepted :
      (run tape
        (selectedRelaxedThroughBeforeMarkerScript positiveTransfer binding body)
        oracle).1 = some (.ok success, returnedDigest)) :
    (run tape (semanticScript positiveTransfer binding body) oracle).1 =
      some (.ok success.semantic) := by
  unfold selectedRelaxedThroughBeforeMarkerScript at accepted
  rw [run_bind] at accepted
  cases semanticRun :
      (run tape (semanticScript positiveTransfer binding body) oracle).1 with
  | none => simp [semanticRun] at accepted
  | some semanticResult =>
    cases semanticResult with
    | error error => simp [semanticRun, FSOracleExecution.run] at accepted
    | ok semantic =>
      simp only [semanticRun] at accepted
      rw [run_bind] at accepted
      let semanticOracle :=
        (run tape (semanticScript positiveTransfer binding body) oracle).2
      let afterPoints := absorb tape
        ({ digest := semantic.finalDigest, oracle := semanticOracle } :
          FSBoundedTranscript.Transcript)
        49 (pointClaimBytes body)
      have pointRun :
          run tape
            (absorbScript semantic.finalDigest 49 (pointClaimBytes body))
            semanticOracle = (some afterPoints.digest, afterPoints.oracle) := by
        exact run_absorb tape
          ({ digest := semantic.finalDigest, oracle := semanticOracle } :
            FSBoundedTranscript.Transcript)
          49 (pointClaimBytes body)
      dsimp only [semanticOracle] at pointRun
      rw [pointRun] at accepted
      simp only [Prod.fst, Prod.snd, run_map] at accepted
      cases suffixRun :
          (run tape
            (selectedBeforeMarkerScript body semantic.z afterPoints.digest)
            afterPoints.oracle).1 with
      | none => simp [suffixRun] at accepted
      | some selectedResult =>
        rcases selectedResult with ⟨selectedResult, selectedDigest⟩
        cases selectedResult with
        | error error => simp [suffixRun] at accepted
        | ok before =>
          simp only [suffixRun, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at accepted
          have same :
              ({ semantic := semantic, before := before } :
                BeforeMarkerSuccess body) = success :=
            Except.ok.inj accepted.1
          have sameSemantic : semantic = success.semantic :=
            congrArg BeforeMarkerSuccess.semantic same
          simpa only [sameSemantic] using semanticRun

/-- The canonical parser fact for the semantic result embedded in a successful
relaxed output.  The run premise is deliberately the semantic-round prefix,
and `successful_run_has_same_body_wire` supplies the same-body witness.
The enclosing root's success-to-semantic-run projection is the next scheduler
corollary, once that root module is constructed.
-/
theorem embedded_semantic_run_has_canonical_body
    (positiveTransfer : Bool) (binding : Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) (oracle : Oracle)
    (semantic : FSLiveSemanticPrefix.Success)
    (semanticRun :
      (run tape (semanticScript positiveTransfer binding body) oracle).1 =
        some (.ok semantic)) :
    exists wire, SameBodySemanticWire.parse body = some wire /\
      AspisV8.SameBodySequentialCodec.fields (body.map UInt8.toFin) =
        some wire.values := by
  exact successful_run_has_same_body_wire positiveTransfer binding body tape
    oracle semantic semanticRun

/-- The relaxed before-marker run itself supplies canonical same-body parse
evidence; callers do not provide a separate semantic-run premise. -/
theorem successful_before_marker_has_canonical_body
    (positiveTransfer : Bool) (binding : Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) (oracle : Oracle)
    (success : BeforeMarkerSuccess body) (returnedDigest : Block)
    (accepted :
      (run tape
        (selectedRelaxedThroughBeforeMarkerScript positiveTransfer binding body)
        oracle).1 = some (.ok success, returnedDigest)) :
    exists wire, SameBodySemanticWire.parse body = some wire /\
      AspisV8.SameBodySequentialCodec.fields (body.map UInt8.toFin) =
        some wire.values := by
  apply embedded_semantic_run_has_canonical_body positiveTransfer binding body
    tape oracle success.semantic
  exact successful_before_marker_projects_semantic_run positiveTransfer binding
    body tape oracle success returnedDigest accepted

#print axioms selected_prefix_numeric_budget
#print axioms selected_before_marker_numeric_budget
#print axioms selectedRelaxedThroughBeforeMarker_call_bound
#print axioms selectedRelaxedThroughAlpha_call_bound
#print axioms selectedRelaxedThroughBeforeMarker_fresh_bound
#print axioms selectedRelaxedThroughAlpha_fresh_bound
#print axioms successful_output_uses_dynamic_semantic_z
#print axioms embedded_semantic_run_has_canonical_body
#print axioms successful_before_marker_has_canonical_body

end
end AspisV8Completion.FSV8S7SelectedSourcePrefixBudget
