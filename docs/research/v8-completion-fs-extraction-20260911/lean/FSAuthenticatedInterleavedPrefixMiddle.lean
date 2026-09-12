import FSLiveSourceFunctionalMiddle
import FSInterleavedSelectedIncrementBoundary

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000

namespace AspisV8Completion.FSAuthenticatedInterleavedPrefixMiddle
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSExposureOrder
open FSV8PostOODGammaScript FSLiveSourceFunctionalMiddle
open FSQuerySchedule
open FSInterleavedSelectedIncrementBoundary
open AspisV8Completion.ExtractionCollectorAuthenticatedReplayable
open FSV7PrefixBridge

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV7OODBodyScript.Point
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

inductive Error where
  | prefix (error : Sum FSOODSampler.Error FSNonzeroQM31.Error)
  | middle (error : FSLiveSourceFunctionalMiddle.Error)
  | suffix (error : InterleavedError)
  | invalidSchedule
  deriving DecidableEq

structure Partial (body : Bytes) (z : Fin 10 → K) where
  out : OODResult
  gamma : K
  middle : FSLiveSourceFunctionalMiddle.Success out gamma body z

structure Record (body : Bytes) (z : Fin 10 → K) where
  out : OODResult
  gamma : K
  middle : FSLiveSourceFunctionalMiddle.Success out gamma body z
  suffix : InterleavedSuccess

noncomputable def suffixContinuation (cuts : FSBoundedTranscript.RootCuts)
    (body : Bytes) (z : Fin 10 → K) (digest : Block)
    (p : Partial body z) :
    Script Bytes Block (Except Error (Record body z) × Block) 1038 := by
  classical
  if h : ValidAccepted p.middle.middle.queries ∧
      p.middle.middle.queries.length = 22 then
    let schedule := scheduleOf p.middle.middle.queries h.1 h.2
    exact bind (m := 0)
      (interleavedSelectedSuffix cuts schedule.positions body
        digest p.middle.functional.data
        p.middle.middle.alpha0 p.middle.middle.rho) fun suffixDraw =>
      .done (match suffixDraw.1 with
        | .error e => (Except.error (.suffix e), suffixDraw.2)
        | .ok suffix =>
            (Except.ok (Record.mk p.out p.gamma p.middle suffix), suffixDraw.2))
  else
    exact .done (Except.error .invalidSchedule, digest)

abbrev middleBudget : Nat :=
  (198 + 1 + 2*8 + 1 + 1) + 66 + 1 + 1 + 66*3 + 1 + 1 + 1 + 66*3 + 1

/- The digest is intentionally an explicit continuation input; this stage
does not fabricate the prefix state. -/
def middleContinuationAt (body : Bytes) (z : Fin 10 → K)
    (out : OODResult) (gamma : K) (digest : Block) :
    Script Bytes Block (Except Error (Partial body z) × Block) middleBudget := by
  classical
  exact bind (m := 0) (FSLiveSourceFunctionalMiddle.middleScript out gamma body z digest)
    fun middleDraw =>
    .done (match middleDraw.1 with
      | .error e => (Except.error (.middle e), middleDraw.2)
      | .ok middle =>
          (Except.ok { out := out, gamma := gamma, middle := middle }, middleDraw.2))

noncomputable def prefixMiddleScript {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block) :
    Script Bytes Block (Except Error (Partial body z) × Block)
      (middleBudget + (1 + 3*66 + (1+m+594+1+n+198))) := by
  classical
  exact FSTranscriptScript.bind (m := middleBudget)
    (sourceThenGammaScript firstWork secondWork body digest) fun prefixDraw =>
    match prefixDraw.1 with
    | .error e => .done (Except.error (.prefix e), prefixDraw.2)
    | .ok (out, gamma) => middleContinuationAt body z out gamma prefixDraw.2

noncomputable def wholeStagedScript {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : FSBoundedTranscript.RootCuts)
    (body : Bytes) (digest : Block) :
    Script Bytes Block (Except Error (Record body z) × Block)
      (1038 + (middleBudget + (1 + 3*66 + (1+m+594+1+n+198)))) := by
  classical
  exact FSTranscriptScript.bind (m := 1038)
    (prefixMiddleScript firstWork secondWork z body digest) fun p =>
      match p.1 with
      | .error e => .done (Except.error e, p.2)
      | .ok pp => suffixContinuation cuts body z p.2 pp

#print axioms wholeStagedScript

theorem successful_wholeStaged_components {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : FSBoundedTranscript.RootCuts)
    (body : Bytes) (digest : Block) (tape : FSBoundedTranscript.Tape)
    (oracle : FSBoundedTranscript.Oracle)
    (record : Record body z) (finalDigest : Block)
    (success :
      (run tape (wholeStagedScript firstWork secondWork z cuts body digest)
        oracle).1 = some (.ok record, finalDigest)) :
    ∃ staged middleDigest,
      (run tape (prefixMiddleScript firstWork secondWork z body digest) oracle).1 =
        some (.ok staged, middleDigest) ∧
      (run tape (suffixContinuation cuts body z middleDigest staged)
        (run tape (prefixMiddleScript firstWork secondWork z body digest)
          oracle).2).1 = some (.ok record, finalDigest) := by
  unfold wholeStagedScript at success
  rw [run_bind] at success
  cases hp :
      (run tape (prefixMiddleScript firstWork secondWork z body digest) oracle).1 with
  | none => simp [hp] at success
  | some pv =>
    rcases pv with ⟨pr, pd⟩
    cases pr with
    | error e => simp [hp, run] at success
    | ok staged =>
      simp only [hp] at success
      exact ⟨staged, pd, rfl, success⟩

theorem successful_suffixContinuation_components
    (cuts : FSBoundedTranscript.RootCuts) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (staged : Partial body z) (tape : FSBoundedTranscript.Tape)
    (oracle : FSBoundedTranscript.Oracle) (record : Record body z)
    (finalDigest : Block)
    (success :
      (run tape (suffixContinuation cuts body z digest staged) oracle).1 =
        some (.ok record, finalDigest)) :
    ∃ valid count,
      ValidAccepted staged.middle.middle.queries ∧
        staged.middle.middle.queries.length = 22 ∧
        (run tape (interleavedSelectedSuffix cuts
          (scheduleOf staged.middle.middle.queries valid count).positions body
          digest staged.middle.functional.data staged.middle.middle.alpha0
          staged.middle.middle.rho) oracle).1 =
        some (.ok record.suffix, finalDigest) := by
  unfold suffixContinuation at success
  by_cases h : ValidAccepted staged.middle.middle.queries ∧
      staged.middle.middle.queries.length = 22
  · refine ⟨h.1, h.2, h.1, h.2, ?_⟩
    rw [dif_pos h, run_bind] at success
    cases interleavedRun :
        (run tape (interleavedSelectedSuffix cuts
          (scheduleOf staged.middle.middle.queries h.1 h.2).positions body
          digest staged.middle.functional.data staged.middle.middle.alpha0
          staged.middle.middle.rho) oracle).1 with
    | none => simp [interleavedRun] at success
    | some value =>
      rcases value with ⟨result, resultDigest⟩
      cases result with
      | error e => simp [interleavedRun, run] at success
      | ok suffix =>
        simp only [interleavedRun, run] at success
        have pairEq := Option.some.inj success
        have recordEq := Except.ok.inj (congrArg Prod.fst pairEq)
        have digestEq := congrArg Prod.snd pairEq
        have resultDigestEq : resultDigest = finalDigest := by
          simpa using digestEq
        subst record
        simpa [resultDigestEq] using interleavedRun
  · rw [dif_neg h] at success
    simp [run] at success

#check successful_wholeStaged_components
#check successful_suffixContinuation_components
#print axioms middleContinuationAt
#print axioms successful_wholeStaged_components
#print axioms successful_suffixContinuation_components
end AspisV8Completion.FSAuthenticatedInterleavedPrefixMiddle
