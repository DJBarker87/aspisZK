import FSV7SampledBodyScript
import FSNonzeroQM31

/-! Insert the selected query-batch profile absorption and bounded nonzero rho
draw between the derived q22 schedule and the authenticated opening hashes.
This closes a deterministic ordering omission in `FSV7SampledBodyScript`; the
incoming transcript and random-oracle law remain explicit obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7SampledRhoBodyScript
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSQuerySampler FSQuerySchedule
open FSV7PrefixBridge FSV7SelectedBodyScript FSV7SampledBodyScript
open AspisV8Completion.FSNonzeroQM31
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths AspisV8.SelectedWireMerkleRun
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact

/-- Literal ASCII bytes of `AV8/query-batch/v1`; Rust label PROFILE is 1. -/
def queryBatchProfile : List UInt8 :=
  [65,86,56,47,113,117,101,114,121,45,98,97,116,99,104,47,118,49]

def afterSchedule (tape : Tape) (before : Transcript) (cuts : RootCuts)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) (returned : List Nat)
    (sample : (reference tape 8 (beforeQueries tape before body) [] 0).1 = some returned) :
    Option (Schedule × K × Option OrderedRawQueryLog) × Oracle :=
  let schedule := from_success tape (beforeQueries tape before body) returned sample
  let sampledState := (reference tape 8 (beforeQueries tape before body) [] 0).2
  let profileState := absorb tape sampledState 1 queryBatchProfile
  let rhoDraw := nonzero tape 3 profileState
  match rhoDraw.1 with
  | .error _ => (none, rhoDraw.2.oracle)
  | .ok rho =>
      let checked := run tape (selectedScript cuts (positionsOf schedule) body) rhoDraw.2.oracle
      (some (schedule, rho, checked.1), checked.2)

def sampledRhoBody (tape : Tape) (before : Transcript) (cuts : RootCuts)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) :
    Option (Schedule × K × Option OrderedRawQueryLog) × Oracle :=
  let sampled := reference tape 8 (beforeQueries tape before body) [] 0
  FSOptionBranch.branch sampled.1 (none, sampled.2.oracle)
    (fun returned success => afterSchedule tape before cuts body returned success)

theorem sampled_rho_body_some (tape : Tape) (before : Transcript) (cuts : RootCuts)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) (returned : List Nat)
    (sample : (reference tape 8 (beforeQueries tape before body) [] 0).1 = some returned) :
    sampledRhoBody tape before cuts body = afterSchedule tape before cuts body returned sample := by
  unfold sampledRhoBody
  dsimp only
  simpa only using FSOptionBranch.some_branch
    (reference tape 8 (beforeQueries tape before body) [] 0).1
    (none, (reference tape 8 (beforeQueries tape before body) [] 0).2.oracle)
    (fun actual actualSample => afterSchedule tape before cuts body actual actualSample)
    returned sample

theorem after_schedule_ok (tape : Tape) (before : Transcript) (cuts : RootCuts)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) (returned : List Nat)
    (sample : (reference tape 8 (beforeQueries tape before body) [] 0).1 = some returned)
    (rho : K)
    (rhoOk : (nonzero tape 3 (absorb tape
      (reference tape 8 (beforeQueries tape before body) [] 0).2
      1 queryBatchProfile)).1 = .ok rho) :
    afterSchedule tape before cuts body returned sample =
      let schedule := from_success tape (beforeQueries tape before body) returned sample
      let rhoState := (nonzero tape 3 (absorb tape
        (reference tape 8 (beforeQueries tape before body) [] 0).2
        1 queryBatchProfile)).2
      let checked := run tape (selectedScript cuts (positionsOf schedule) body) rhoState.oracle
      (some (schedule, rho, checked.1), checked.2) := by
  unfold afterSchedule
  dsimp only
  rw [rhoOk]

/-- The selected ordering is now schedule, PROFILE/query-batch, nonzero rho,
then leaf/node authentication.  Rho is the actual bounded sampler output and
the Merkle positions are the actual q22 sampler output. -/
theorem sampled_rho_body_constructs (tape : Tape) (before : Transcript) (cuts : RootCuts)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte)
    (schedule : Schedule) (rho : K) (trace : OrderedRawQueryLog)
    (valid : FSFirstFresh.ValidHistory before.oracle)
    (success : (sampledRhoBody tape before cuts body).1 =
      some (schedule, rho, some trace)) :
    rho ≠ 0 ∧ Function.Injective (positionsOf schedule) ∧
    ∃ merkle : SuccessfulMerkleRun (oldView (sampledRhoBody tape before cuts body).2)
        (positionsOf schedule) body,
      merkle.trace = trace ∧ merkle.wire.roots 0 = root208 cuts.c1 ∧
      merkle.wire.roots 1 = root208 cuts.c2 ∧
      TraceIncludedInLog (leafLog (positionsOf schedule) (wireRecords merkle.wire) ++ merkle.trace)
        (oldLog (sampledRhoBody tape before cuts body).2) := by
  cases sample : (reference tape 8 (beforeQueries tape before body) [] 0).1 with
  | none =>
      unfold sampledRhoBody at success
      dsimp only at success
      rw [FSOptionBranch.none_branch _ _ _ sample] at success
      contradiction
  | some returned =>
      rw [sampled_rho_body_some tape before cuts body returned sample] at success ⊢
      let sampledState := (reference tape 8 (beforeQueries tape before body) [] 0).2
      let profileState := absorb tape sampledState 1 queryBatchProfile
      cases rhoResult : (nonzero tape 3 profileState).1 with
      | error error =>
          unfold afterSchedule at success
          dsimp only [sampledState, profileState] at success
          rw [rhoResult] at success
          contradiction
      | ok actualRho =>
          rw [after_schedule_ok tape before cuts body returned sample actualRho rhoResult] at success ⊢
          have both := Option.some.inj success
          have scheduleSame : from_success tape (beforeQueries tape before body) returned sample = schedule :=
            congrArg Prod.fst both
          have rhoSame : actualRho = rho := congrArg (fun x => x.2.1) both
          subst schedule
          subst rho
          have merkleSuccess := congrArg (fun x => x.2.2) both
          have sampledValid := queries_valid tape 8
            (beforeQueries tape before body).digest (beforeQueries tape before body).oracle [] 0
            (before_queries_valid tape before body valid)
          have profileValid := absorb_valid tape sampledState 1 queryBatchProfile sampledValid
          have rhoValid := nonzero_valid tape 3 profileState profileValid
          refine ⟨nonzero_success_ne tape 3 profileState actualRho rhoResult, ?_, ?_⟩
          · exact (from_success tape (beforeQueries tape before body) returned sample).distinct
          · exact selected_constructs tape cuts _ body _ trace rhoValid.coherent merkleSuccess

#print sampled_rho_body_constructs
#print axioms sampled_rho_body_some
#print axioms after_schedule_ok
#print axioms sampled_rho_body_constructs
end AspisV8Completion.FSV7SampledRhoBodyScript
