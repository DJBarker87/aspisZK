import ExtractionCollectorReplayableSource
import FSLiveSourceFunctionalMiddle

/-!
# Replayable source with fallible functional construction

One chronological script now joins the source/OOD/gamma prefix, the
source-driven fallible compact-functional middle, and the existing live later
relation suffix.  Public `z` and the authenticated increment producer remain
the two explicit source inputs.  This file performs no terminal acceptance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.ExtractionCollectorFallibleFunctionalSource

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript
open FSLiveLaterRelationSuffix
open FSLiveSourceFunctionalMiddle

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV7OODBodyScript.Point
abbrev OODResult := FSV7OODBodyScript.Result
abbrev K := FSNonzeroQM31.K
abbrev PrefixError := Sum FSOODSampler.Error FSNonzeroQM31.Error

noncomputable section

inductive Error where
  | prefix (error : PrefixError)
  | middle (error : FSLiveSourceFunctionalMiddle.Error)
  | later (error : FSLiveLaterRelationSuffix.Error)
  deriving DecidableEq

structure Record where
  body : Bytes
  ood : OODResult
  gamma : K
  z : Fin 10 → K
  middle : FSLiveSourceFunctionalMiddle.Success ood gamma body z
  later : FSLiveLaterRelationSuffix.Success

-- The explicit order avoids a hidden externally supplied selected-middle view.
def Record.selectedMiddle (record : Record) :
    FSLiveSelectedMiddleQueryRho.Success := record.middle.middle

def replayableScript {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (increment : IncrementProducer)
    (body : Bytes) (digest : Block) :=
  FSTranscriptScript.bind
      (sourceThenGammaScript firstWork secondWork body digest) fun prefixDraw =>
    match prefixDraw.1 with
    | .error e => .done (Except.error (Error.prefix e), prefixDraw.2)
    | .ok (out, gamma) =>
      FSTranscriptScript.bind
        (FSLiveSourceFunctionalMiddle.middleScript out gamma body z prefixDraw.2)
        fun middleDraw =>
          match middleDraw.1 with
          | .error e => .done (Except.error (Error.middle e), middleDraw.2)
          | .ok middle =>
            FSTranscriptScript.bind (m := 0)
                (laterScript increment out gamma middle.middle body middleDraw.2)
              fun laterDraw =>
                .done (match laterDraw.1 with
                  | .error e => (Except.error (Error.later e), laterDraw.2)
                  | .ok later =>
                    (Except.ok
                      ({ body := body, ood := out, gamma := gamma,
                         z := z, middle := middle, later := later } : Record),
                      laterDraw.2))

/-- A successful run decomposes at both exact chronological boundaries. -/
theorem successful_run_components {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (increment : IncrementProducer)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle)
    (record : Record) (finalDigest : Block)
    (success :
      (run tape (replayableScript firstWork secondWork z increment body digest)
        oracle).1 = some (Except.ok record, finalDigest)) :
    ∃ out gamma prefixDigest middle middleDigest later,
      (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).1 =
        some (Except.ok (out, gamma), prefixDigest) ∧
      (run tape (FSLiveSourceFunctionalMiddle.middleScript
          out gamma body z prefixDigest)
        (run tape (sourceThenGammaScript firstWork secondWork body digest)
          oracle).2).1 = some (Except.ok middle, middleDigest) ∧
      (run tape (laterScript increment out gamma middle.middle body middleDigest)
        (run tape (FSLiveSourceFunctionalMiddle.middleScript
            out gamma body z prefixDigest)
          (run tape (sourceThenGammaScript firstWork secondWork body digest)
            oracle).2).2).1 = some (Except.ok later, finalDigest) ∧
      record = Record.mk body out gamma z middle later := by
  unfold replayableScript at success
  rw [run_bind] at success
  cases prefixRun :
      (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).1 with
  | none => simp [prefixRun] at success
  | some prefixValue =>
    rcases prefixValue with ⟨prefixResult, prefixDigest⟩
    cases prefixResult with
    | error e => simp [prefixRun, run] at success
    | ok pair =>
      rcases pair with ⟨out, gamma⟩
      simp only [prefixRun] at success
      rw [run_bind] at success
      cases middleRun :
          (run tape (FSLiveSourceFunctionalMiddle.middleScript
            out gamma body z prefixDigest)
            (run tape (sourceThenGammaScript firstWork secondWork body digest)
              oracle).2).1 with
      | none => simp [middleRun] at success
      | some middleValue =>
        rcases middleValue with ⟨middleResult, middleDigest⟩
        cases middleResult with
        | error e => simp [middleRun, run] at success
        | ok middle =>
          simp only [middleRun] at success
          rw [run_bind] at success
          cases laterRun :
              (run tape (laterScript increment out gamma middle.middle body middleDigest)
                (run tape (FSLiveSourceFunctionalMiddle.middleScript
                  out gamma body z prefixDigest)
                  (run tape (sourceThenGammaScript firstWork secondWork body digest)
                    oracle).2).2).1 with
          | none => simp [laterRun] at success
          | some laterValue =>
            rcases laterValue with ⟨laterResult, laterDigest⟩
            cases laterResult with
            | error e => simp [laterRun, run] at success
            | ok later =>
              simp [laterRun, run] at success
              rcases success with ⟨rfl, rfl⟩
              exact ⟨out, gamma, prefixDigest, middle, middleDigest, later,
                rfl, middleRun, laterRun, rfl⟩

/-- The same returned record carries the fallible functional constructor's
checked OOD data and exact gamma, without an additional acceptance premise. -/
theorem successful_record_functional_provenance {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (increment : IncrementProducer)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle)
    (record : Record) (finalDigest : Block)
    (success :
      (run tape (replayableScript firstWork secondWork z increment body digest)
        oracle).1 = some (Except.ok record, finalDigest)) :
    SameBodyFunctionalProducerSource.fromInputs record.ood record.gamma
        record.middle.middle.kappa record.body record.z =
          some record.middle.functional ∧
      record.middle.functional.data.Checked ∧
      record.middle.functional.data.gamma = record.gamma := by
  exact ⟨record.middle.functionalRun,
    SameBodyFunctionalProducerSource.fromInputs_data_checked _ _ _ _ _ _
      record.middle.functionalRun,
    SameBodyFunctionalProducerSource.fromInputs_data_gamma _ _ _ _ _ _
      record.middle.functionalRun⟩

#print axioms successful_run_components
#print axioms successful_record_functional_provenance

end
end AspisV8Completion.ExtractionCollectorFallibleFunctionalSource
