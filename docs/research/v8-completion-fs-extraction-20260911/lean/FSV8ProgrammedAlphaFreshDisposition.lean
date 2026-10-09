import FSV8ProgrammedAlphaFreshEntryProvenance

/-!
# Fresh-source provenance for the programmed alpha candidate

This leaf strengthens the two verifier-prefix insertion cases.  If the exact
candidate lookup was absent at the beginning of a machine segment and present
at its end, that segment contains an actual fresh creator record.  The two
remaining cached-root cases and the genuinely absent candidate stay distinct.

No probability, target-event inclusion, or sampler law is claimed here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000

namespace AspisV8Completion.FSV8ProgrammedAlphaFreshDisposition

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73VerifierOracleStability
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8V7OracleMachineBridge
open FSV8PostOODGammaScript
open FSV8ExecutablePreAlphaFactorization
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaPrefixInsertionProvenance
open FSV8ProgrammedAlphaFreshEntryProvenance

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- The same five-way causal partition with an actual fresh creator for every
entry first introduced by one of the two verifier segments. -/
inductive FreshCausalAlphaDisposition
    (root sourceState candidateState : OracleState)
    (actor : QueryActor) (input : ShaInput) : Prop where
  | priorAdversary
      (record : QueryRecord)
      (member : record ∈ freezeAdversaryQ1 root)
      (inputEq : record.input = input)
  | priorTarget
      (noAdversary : NoPriorAdversaryInput root input)
      (entry : TableEntry)
      (lookup : lookupEntry root input = some entry)
  | introducedDuringSource
      (noAdversary : NoPriorAdversaryInput root input)
      (rootAbsent : lookupEntry root input = none)
      (entry : TableEntry)
      (sourceLookup : lookupEntry sourceState input = some entry)
      (record : QueryRecord)
      (member : record ∈ historySince root sourceState)
      (actorEq : record.actor = actor)
      (fresh : record.origin = .fresh)
      (inputEq : record.input = input)
      (outputEq : record.output = entry.output)
      (entryEq : entry = freshTableEntryOfRecord record)
  | introducedDuringPreAlpha
      (noAdversary : NoPriorAdversaryInput root input)
      (rootAbsent : lookupEntry root input = none)
      (sourceAbsent : lookupEntry sourceState input = none)
      (entry : TableEntry)
      (candidateLookup : lookupEntry candidateState input = some entry)
      (record : QueryRecord)
      (member : record ∈ historySince sourceState candidateState)
      (actorEq : record.actor = actor)
      (fresh : record.origin = .fresh)
      (inputEq : record.input = input)
      (outputEq : record.output = entry.output)
      (entryEq : entry = freshTableEntryOfRecord record)
  | freshAtCandidate
      (noAdversary : NoPriorAdversaryInput root input)
      (rootAbsent : lookupEntry root input = none)
      (candidateAbsent : lookupEntry candidateState input = none)

/-- Upgrade the exact source/pre-alpha insertion alternatives to fresh-source
records.  The proof uses lookup absence at the real segment boundary; it does
not infer freshness from a matching history record. -/
theorem strong_disposition_constructs_fresh_disposition
    {steps : Nat}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fuel : Nat)
    (out : FSV7OODBodyScript.Result) (gamma : K)
    (sourceDigest : Block)
    (boundary : PreAlpha out gamma body z)
    (strong :
      let sourceRun := sourceMachineRun finiteTape limits actor firstWork
        secondWork body digest v7 fuel
      let preRun := preAlphaMachineRun finiteTape limits actor firstWork
        secondWork body digest v7 fuel out gamma z sourceDigest
      StrongCausalAlphaDisposition v7 sourceRun.oracle preRun.oracle actor
        (List.ofFn boundary.digest ++ [1])) :
    let sourceRun := sourceMachineRun finiteTape limits actor firstWork
      secondWork body digest v7 fuel
    let preRun := preAlphaMachineRun finiteTape limits actor firstWork
      secondWork body digest v7 fuel out gamma z sourceDigest
    FreshCausalAlphaDisposition v7 sourceRun.oracle preRun.oracle actor
      (List.ofFn boundary.digest ++ [1]) := by
  let sourceRun := sourceMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel
  let preRun := preAlphaMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel out gamma z sourceDigest
  cases strong with
  | priorAdversary record member inputEq =>
      exact .priorAdversary record member inputEq
  | priorTarget noAdversary entry lookup =>
      exact .priorTarget noAdversary entry lookup
  | freshAtCandidate noAdversary rootAbsent candidateAbsent =>
      exact .freshAtCandidate noAdversary rootAbsent candidateAbsent
  | introducedDuringSource noAdversary rootAbsent sourceEntry _candidateEntry
      sourceLookup _candidateLookup _oldRecord _oldMember _oldActor
      _oldInput _oldOutput =>
      obtain ⟨record, member, actorEq, fresh, inputEq, outputEq, entryEq⟩ :=
        run_machine_lookup_of_initially_absent_is_fresh
          (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
          (compileScript
            (sourceThenGammaScript firstWork secondWork body digest))
          (List.ofFn boundary.digest ++ [1]) sourceEntry rootAbsent
          (by simpa [sourceRun, sourceMachineRun] using sourceLookup)
      exact .introducedDuringSource noAdversary rootAbsent sourceEntry
        sourceLookup record (by simpa [sourceRun, sourceMachineRun] using member)
        actorEq fresh inputEq outputEq entryEq
  | introducedDuringPreAlpha noAdversary rootAbsent entry sourceAbsent
      candidateLookup _oldRecord _oldMember _oldActor _oldInput _oldOutput =>
      obtain ⟨record, member, actorEq, fresh, inputEq, outputEq, entryEq⟩ :=
        run_machine_lookup_of_initially_absent_is_fresh
          (controllerFromFreshAnswerTape finiteTape) limits actor
          (fuel - sourceRun.steps) sourceRun.oracle
          (compileScript (preAlphaScript out gamma body z sourceDigest))
          (List.ofFn boundary.digest ++ [1]) entry sourceAbsent
          (by simpa [preRun, preAlphaMachineRun] using candidateLookup)
      exact .introducedDuringPreAlpha noAdversary rootAbsent sourceAbsent entry
        candidateLookup record
        (by simpa [sourceRun, preRun, preAlphaMachineRun] using member)
        actorEq fresh inputEq outputEq entryEq

/-- The same source-shaped fresh disposition can be constructed directly at
any fixed boundary returned by the prefix.  This avoids pairing the marker cut
with a separately existentialized candidate-disposition witness. -/
theorem source_runs_construct_fresh_disposition
    {steps : Nat}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fuel : Nat)
    (out : FSV7OODBodyScript.Result) (gamma : K)
    (sourceDigest : Block)
    (boundary : PreAlpha out gamma body z) :
    let sourceRun := sourceMachineRun finiteTape limits actor firstWork
      secondWork body digest v7 fuel
    let preRun := preAlphaMachineRun finiteTape limits actor firstWork
      secondWork body digest v7 fuel out gamma z sourceDigest
    FreshCausalAlphaDisposition v7 sourceRun.oracle preRun.oracle actor
      (List.ofFn boundary.digest ++ [1]) := by
  classical
  let input := List.ofFn boundary.digest ++ [1]
  let sourceRun := sourceMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel
  let preRun := preAlphaMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel out gamma z sourceDigest
  by_cases adversary : ∃ record,
      record ∈ freezeAdversaryQ1 v7 ∧ record.input = input
  · exact .priorAdversary (Classical.choose adversary)
      (Classical.choose_spec adversary).1
      (Classical.choose_spec adversary).2
  · cases rootLookup : lookupEntry v7 input with
    | some entry =>
        exact .priorTarget adversary entry rootLookup
    | none =>
        cases sourceLookup : lookupEntry sourceRun.oracle input with
        | some entry =>
            obtain ⟨record, member, actorEq, fresh, inputEq, outputEq,
                entryEq⟩ :=
              run_machine_lookup_of_initially_absent_is_fresh
                (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
                (compileScript
                  (sourceThenGammaScript firstWork secondWork body digest))
                input entry rootLookup
                (by simpa [sourceRun, sourceMachineRun] using sourceLookup)
            exact .introducedDuringSource adversary rootLookup entry sourceLookup
              record (by simpa [sourceRun, sourceMachineRun] using member)
              actorEq fresh inputEq outputEq entryEq
        | none =>
            cases preLookup : lookupEntry preRun.oracle input with
            | none =>
                exact .freshAtCandidate adversary rootLookup preLookup
            | some entry =>
                obtain ⟨record, member, actorEq, fresh, inputEq, outputEq,
                    entryEq⟩ :=
                  run_machine_lookup_of_initially_absent_is_fresh
                    (controllerFromFreshAnswerTape finiteTape) limits actor
                    (fuel - sourceRun.steps) sourceRun.oracle
                    (compileScript
                      (preAlphaScript out gamma body z sourceDigest))
                    input entry sourceLookup
                    (by simpa [preRun, preAlphaMachineRun] using preLookup)
                exact .introducedDuringPreAlpha adversary rootLookup sourceLookup
                  entry preLookup record
                  (by simpa [sourceRun, preRun, preAlphaMachineRun] using member)
                  actorEq fresh inputEq outputEq entryEq

#print axioms strong_disposition_constructs_fresh_disposition
#print axioms source_runs_construct_fresh_disposition

end
end AspisV8Completion.FSV8ProgrammedAlphaFreshDisposition
