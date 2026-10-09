import SameBodyAuthenticatedIncrement
import FSLiveSelectedMiddleQueryRho
import FSQuerySchedule

/-!
# Live q22 schedule to authenticated increment

This leaf constructs the typed `Fin 22 -> Fin 262144` query schedule from the
list returned by the same successful live middle/query/rho execution.  The
schedule is then passed to `SameBodyAuthenticatedIncrement.prepare` by
construction; no caller-supplied schedule equality is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.SameBodyLivePreparedIncrement

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSNonzeroQM31 FSLiveQueryRhoSuffix FSQuerySchedule
open FSLiveSelectedMiddleQueryRho
open SameBodyAuthenticatedIncrement
open AspisPool.V7MerkleQueryGrammar
open AspisV8.SelectedQuotientOriginal
open AspisV8.AuthenticatedEarlyC1Prefix
open AspisV8.OODInterpolant

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Transcript := FSBoundedTranscript.Transcript
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K

noncomputable section

/-- Removing the success wrapper around the literal suffix does not invent a
schedule: the returned query list and rho are forced by constructor equality. -/
theorem wrapped_suffix_success (body : Bytes) (tape : Tape) (start : Transcript)
    (kappa tau alpha0 : K) (success : Success) (finalDigest : Block)
    (accepted :
      (run tape
        (bind (m := 0) (queryRhoScript body start.digest) fun suffixDraw =>
          .done (match suffixDraw.1 with
            | .error e => (Except.error (Error.suffix e), suffixDraw.2)
            | .ok (queries, rho) =>
              (Except.ok (Success.mk kappa tau alpha0 queries rho), suffixDraw.2)))
        start.oracle).1 = some (.ok success, finalDigest)) :
    (run tape (queryRhoScript body start.digest) start.oracle).1 =
      some (.ok (success.queries, success.rho), finalDigest) := by
  rw [run_bind] at accepted
  cases suffixRun :
      (run tape (queryRhoScript body start.digest) start.oracle).1 with
  | none => simp [suffixRun] at accepted
  | some suffixValue =>
    rcases suffixValue with ⟨suffixResult, suffixDigest⟩
    cases suffixResult with
    | error e => simp [suffixRun, FSOracleExecution.run] at accepted
    | ok pair =>
      rcases pair with ⟨queries, rho⟩
      simp only [suffixRun, FSOracleExecution.run] at accepted
      have same := Option.some.inj accepted
      have resultSame := congrArg Prod.fst same
      have digestSame := congrArg Prod.snd same
      cases resultSame
      cases digestSame
      simpa using suffixRun

/-- A successful selected middle run exposes success of its literal
`queryRhoScript` suffix from the exact transcript reached after alpha0. -/
theorem middle_success_has_suffix (producer : FunctionalProducer)
    (out : OODResult) (gamma : K) (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : Oracle) (success : Success) (finalDigest : Block)
    (accepted :
      (run tape (middleQueryRhoScript producer out gamma body digest) oracle).1 =
        some (.ok success, finalDigest)) :
    ∃ start : Transcript,
      (run tape (queryRhoScript body start.digest) start.oracle).1 =
        some (.ok (success.queries, success.rho), finalDigest) := by
  unfold middleQueryRhoScript at accepted
  rw [run_bind] at accepted
  simp only [run_absorb tape (Transcript.mk digest oracle)] at accepted
  rw [run_bind, run_nonzero] at accepted
  simp only [Prod.fst, Prod.snd] at accepted
  split at accepted
  · simp [run] at accepted
  · rw [run_bind, run_absorb] at accepted
    simp only [Prod.fst, Prod.snd] at accepted
    rw [run_bind, run_absorb] at accepted
    simp only [Prod.fst, Prod.snd] at accepted
    rw [run_bind, run_absorb] at accepted
    simp only [Prod.fst, Prod.snd] at accepted
    rw [run_bind, run_nonzero] at accepted
    simp only [Prod.fst, Prod.snd] at accepted
    split at accepted
    · simp [run] at accepted
    · rw [run_bind, run_absorb] at accepted
      simp only [Prod.fst, Prod.snd] at accepted
      rw [run_bind, run_absorb] at accepted
      simp only [Prod.fst, Prod.snd] at accepted
      rw [run_bind, run_candidate] at accepted
      simp only [Prod.fst, Prod.snd] at accepted
      generalize startEq : (candidate tape _).2 = start at accepted
      split at accepted
      · simp [run] at accepted
      · refine ⟨start, ?_⟩
        exact wrapped_suffix_success body tape start _ _ _ success finalDigest accepted

/-- The live returned list itself supplies the q22 validity and length
certificate; rho nonzeroness is obtained from the same suffix trace. -/
theorem middle_success_schedule_facts (producer : FunctionalProducer)
    (out : OODResult) (gamma : K) (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : Oracle) (success : Success) (finalDigest : Block)
    (accepted :
      (run tape (middleQueryRhoScript producer out gamma body digest) oracle).1 =
        some (.ok success, finalDigest)) :
    ValidAccepted success.queries ∧ success.queries.length = 22 ∧
      success.rho ≠ 0 := by
  obtain ⟨start, suffixSuccess⟩ := middle_success_has_suffix producer out gamma
    body digest tape oracle success finalDigest accepted
  have exactRun := trace_exact body tape start
  have traceResult : (trace body tape start).result =
      .ok (success.queries, success.rho) := by
    rw [exactRun] at suffixSuccess
    exact congrArg Prod.fst (Option.some.inj suffixSuccess)
  exact trace_success body tape start success.queries success.rho traceResult

/-- The typed schedule is constructed from the exact successful live list. -/
def liveSchedule (success : Success)
    (valid : ValidAccepted success.queries)
    (count : success.queries.length = 22) : Schedule :=
  scheduleOf success.queries valid count

theorem liveSchedule_values (success : Success)
    (valid : ValidAccepted success.queries)
    (count : success.queries.length = 22) (i : Fin 22) :
    ((liveSchedule success valid count).positions i).val =
      success.queries[i.val]'(by omega) := by
  rfl

/-- Direct constructor from the successful same-execution middle run.  Its
proof arguments are generated by `middle_success_schedule_facts`; there is no
schedule certificate among the theorem inputs. -/
def liveScheduleFromRun (producer : FunctionalProducer)
    (out : OODResult) (gamma : K) (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : Oracle) (success : Success) (finalDigest : Block)
    (accepted :
      (run tape (middleQueryRhoScript producer out gamma body digest) oracle).1 =
        some (.ok success, finalDigest)) : Schedule :=
  let facts := middle_success_schedule_facts producer out gamma body digest
    tape oracle success finalDigest accepted
  scheduleOf success.queries facts.1 facts.2.1

theorem liveScheduleFromRun_values (producer : FunctionalProducer)
    (out : OODResult) (gamma : K) (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : Oracle) (success : Success) (finalDigest : Block)
    (accepted :
      (run tape (middleQueryRhoScript producer out gamma body digest) oracle).1 =
        some (.ok success, finalDigest)) (i : Fin 22) :
    ((liveScheduleFromRun producer out gamma body digest tape oracle success
      finalDigest accepted).positions i).val =
      success.queries[i.val]'(by
        have facts := middle_success_schedule_facts producer out gamma body
          digest tape oracle success finalDigest accepted
        omega) := by
  rfl

/-- Feed only the schedule constructed from the live sampler result into the
authenticated opening pipeline. -/
def prepareFromLive (view : RawHashInput -> Digest208) (body : Bytes)
    (success : Success) (valid : ValidAccepted success.queries)
    (count : success.queries.length = 22) (data : Data (K := K)) :=
  SameBodyAuthenticatedIncrement.prepare view body
    (liveSchedule success valid count).positions data success.alpha0 success.rho

/-- Direct same-run preparation: the authenticated opening pipeline consumes
the typed schedule constructed from the live sampler success. -/
def prepareFromRun (view : RawHashInput -> Digest208)
    (producer : FunctionalProducer) (out : OODResult) (gamma : K)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle)
    (success : Success) (finalDigest : Block)
    (accepted :
      (run tape (middleQueryRhoScript producer out gamma body digest) oracle).1 =
        some (.ok success, finalDigest)) (data : Data (K := K)) :=
  SameBodyAuthenticatedIncrement.prepare view body
    (liveScheduleFromRun producer out gamma body digest tape oracle success
      finalDigest accepted).positions data success.alpha0 success.rho

theorem prepareFromLive_success (view : RawHashInput -> Digest208)
    (body : Bytes) (success : Success)
    (valid : ValidAccepted success.queries)
    (count : success.queries.length = 22) (data : Data (K := K))
    (prepared : SameBodyAuthenticatedIncrement.Prepared view)
    (preparedOk : prepareFromLive view body success valid count data = .ok prepared) :
    prepared.query = (liveSchedule success valid count).positions ∧
      prepared.alpha = success.alpha0 ∧ prepared.rho = success.rho := by
  unfold prepareFromLive SameBodyAuthenticatedIncrement.prepare at preparedOk
  split at preparedOk
  · contradiction
  · cases preparedOk
    exact ⟨rfl, rfl, rfl⟩

theorem prepareFromRun_success (view : RawHashInput -> Digest208)
    (producer : FunctionalProducer) (out : OODResult) (gamma : K)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle)
    (success : Success) (finalDigest : Block)
    (accepted :
      (run tape (middleQueryRhoScript producer out gamma body digest) oracle).1 =
        some (.ok success, finalDigest)) (data : Data (K := K))
    (prepared : SameBodyAuthenticatedIncrement.Prepared view)
    (preparedOk : prepareFromRun view producer out gamma body digest tape oracle
      success finalDigest accepted data = .ok prepared) :
    prepared.query =
        (liveScheduleFromRun producer out gamma body digest tape oracle success
          finalDigest accepted).positions ∧
      prepared.alpha = success.alpha0 ∧ prepared.rho = success.rho := by
  unfold prepareFromRun SameBodyAuthenticatedIncrement.prepare at preparedOk
  split at preparedOk
  · contradiction
  · cases preparedOk
    exact ⟨rfl, rfl, rfl⟩

#print axioms middle_success_has_suffix
#print axioms wrapped_suffix_success
#print axioms middle_success_schedule_facts
#print axioms liveSchedule_values
#print axioms liveScheduleFromRun_values
#print axioms prepareFromLive_success
#print axioms prepareFromRun_success

end
end AspisV8Completion.SameBodyLivePreparedIncrement
