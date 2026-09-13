import FSV8ProgrammedAlphaMarkerHistoryPrefix

/-!
# The actual post-alpha continuation is inside the same whole run

This strengthens the earlier marker-successor prefix result at the other end
of the middle continuation.  The terminal state of the literal successful
`postAlphaScript` is proved to precede the final oracle of the same successful
factored whole verifier.  No independently supplied decomposition or state
equality is used.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 2600

namespace AspisV8Completion.FSV8ProgrammedPostAlphaHistoryPrefix

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSV8V7ProgrammedAlignment
open FSV8PostOODGammaScript FSLiveSourceFunctionalMiddle
open FSAuthenticatedInterleavedPrefixMiddle
open FSV8ExecutablePreAlphaFactorization FSV8ExecutableWholeFactorization
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaCutWitness
open FSV8ReturnedBindKnownPrefix
open FSV8ReturnedBindKnownPrefixCuts

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- The complete post-alpha result is a chronological prefix of the complete
factored verifier result from which its cut witness was constructed. -/
theorem programmed_postAlpha_history_prefix_factored_whole
    {steps : Nat} {tape : Tape}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fs : State Bytes Block) (fuel : Nat)
    (record : Record body z) (finalDigest : Block)
    (aligned : StateAligned tape finiteTape v7 fs)
    (wholeSuccess :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (factoredWholeStagedScript firstWork secondWork z cuts
          body digest))).halt = .returned (.ok record, finalDigest))
    (out : OODResult) (gamma : K) (sourceDigest : Block)
    (boundary : PreAlpha out gamma body z) (preDigest : Block)
    (before : FSV8BeforeAlphaMarkerFactorization.BeforeAlphaMarker
      out gamma body z)
    (middle : Success out gamma body z) (middleResultDigest : Block)
    (cutWitness : ProgrammedAlphaCutWitness (tape := tape) finiteTape limits
      actor firstWork secondWork z body digest v7 fs fuel out gamma sourceDigest
      boundary preDigest before middle middleResultDigest) :
    let sourceRun := sourceMachineRun finiteTape limits actor firstWork
      secondWork body digest v7 fuel
    let middleFuel := fuel - sourceRun.steps
    let preRun := preAlphaMachineRun finiteTape limits actor firstWork secondWork
      body digest v7 fuel out gamma z sourceDigest
    let postAlphaRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      limits actor (middleFuel - preRun.steps) preRun.oracle
      (compileScript (postAlphaScript out gamma body z boundary))
    postAlphaRun.oracle.history <+:
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (factoredWholeStagedScript firstWork secondWork z cuts
          body digest))).oracle.history := by
  let sourceRun := sourceMachineRun finiteTape limits actor firstWork
    secondWork body digest v7 fuel
  let middleFuel := fuel - sourceRun.steps
  let preRun := preAlphaMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel out gamma z sourceDigest
  let postAlphaRun := runMachine (controllerFromFreshAnswerTape finiteTape)
    limits actor (middleFuel - preRun.steps) preRun.oracle
    (compileScript (postAlphaScript out gamma body z boundary))
  have cutCopy := cutWitness
  unfold ProgrammedAlphaCutWitness at cutCopy
  rcases cutCopy with
    ⟨sourceReturned, _sourceFunctional, preReturned, _markerReturned,
      _markerContinuationReturned, _postAlphaReturned, _markerFunctional,
      _markerAligned, _markerContinuationFunctional, _afterMarkerAligned⟩
  obtain ⟨staged, middleDigest, wholePrefixReturned,
      wholeContinuationReturned, _wholeFunctional, wholePrefixAligned,
      wholeOracle⟩ :=
    returned_factoredWhole_constructs_prefixMiddle_cut_with_final_oracle
      limits actor firstWork secondWork z cuts body digest v7 fs fuel record
      finalDigest aligned wholeSuccess
  obtain ⟨out', gamma', sourceDigest', sourcePrefixReturned,
      sourceContinuationReturned, _sourceFunctional', sourcePrefixAligned,
      sourceOracle⟩ :=
    returned_factoredPrefixMiddle_constructs_source_cut_with_final_oracle
      limits actor firstWork secondWork z body digest v7 fs fuel staged
      middleDigest aligned wholePrefixReturned
  have sourceValueExact :
      ((Except.ok (out', gamma') :
          Except (Sum FSOODSampler.Error FSNonzeroQM31.Error)
            (OODResult × K)), sourceDigest') =
        (Except.ok (out, gamma), sourceDigest) := by
    exact MachineHalt.returned.inj
      (sourcePrefixReturned.symm.trans sourceReturned)
  have sourcePairExact : (out', gamma') = (out, gamma) :=
    Except.ok.inj (congrArg Prod.fst sourceValueExact)
  have sourceDigestExact : sourceDigest' = sourceDigest :=
    congrArg Prod.snd sourceValueExact
  have outExact : out' = out := congrArg Prod.fst sourcePairExact
  have gammaExact : gamma' = gamma := congrArg Prod.snd sourcePairExact
  subst out'
  subst gamma'
  subst sourceDigest'
  let sourceFs :=
    (run tape (sourceThenGammaScript firstWork secondWork body digest) fs).2
  obtain ⟨middle', middleDigest', middlePrefixReturned,
      middleContinuationReturned, _middleFunctional, middlePrefixAligned,
      middleOracle⟩ :=
    returned_factoredMiddleContinuationAt_constructs_middle_cut_with_final_oracle
      limits actor body z out gamma sourceDigest sourceRun.oracle sourceFs
      middleFuel staged middleDigest sourcePrefixAligned sourceContinuationReturned
  obtain ⟨boundary', preDigest', prePrefixReturned, postAlphaReturned',
      _preFunctional, prePrefixAligned, preOracle⟩ :=
    returned_factoredMiddle_constructs_preAlpha_cut_with_final_oracle
      limits actor out gamma body z sourceDigest sourceRun.oracle sourceFs
      middleFuel middle' middleDigest' sourcePrefixAligned middlePrefixReturned
  have preValueExact :
      ((Except.ok boundary' :
          Except FSLiveSourceFunctionalMiddle.Error (PreAlpha out gamma body z)),
          preDigest') =
        ((Except.ok boundary :
          Except FSLiveSourceFunctionalMiddle.Error (PreAlpha out gamma body z)),
          preDigest) := by
    exact MachineHalt.returned.inj
      (prePrefixReturned.symm.trans preReturned)
  have boundaryExact : boundary' = boundary :=
    Except.ok.inj (congrArg Prod.fst preValueExact)
  have middleToDone := runMachine_entry_history_prefix_final
    (controllerFromFreshAnswerTape finiteTape) limits actor
    (middleFuel -
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
        middleFuel sourceRun.oracle
        (compileScript
          (factoredMiddleScript out gamma body z sourceDigest))).steps)
    (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
      middleFuel sourceRun.oracle
      (compileScript
        (factoredMiddleScript out gamma body z sourceDigest))).oracle
    (compileScript
      (Script.done
        (Except.ok { out := out, gamma := gamma, middle := middle' },
          middleDigest') :
        Script Bytes Block
          (Except FSAuthenticatedInterleavedPrefixMiddle.Error
            (Partial body z) × Block) 0))
  have prefixToSuffix := runMachine_entry_history_prefix_final
    (controllerFromFreshAnswerTape finiteTape) limits actor
    (fuel -
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript
          (factoredPrefixMiddleScript firstWork secondWork z body digest))).steps)
    (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
      (compileScript
        (factoredPrefixMiddleScript firstWork secondWork z body digest))).oracle
    (compileScript (suffixContinuation cuts body z middleDigest staged))
  calc
    postAlphaRun.oracle.history =
        (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
          middleFuel sourceRun.oracle
          (compileScript
            (factoredMiddleScript out gamma body z sourceDigest))).oracle.history := by
      rw [preOracle, boundaryExact]
      rfl
    _ <+:
        (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
          (middleFuel -
            (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
              middleFuel sourceRun.oracle
              (compileScript
                (factoredMiddleScript out gamma body z sourceDigest))).steps)
          (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
            middleFuel sourceRun.oracle
            (compileScript
              (factoredMiddleScript out gamma body z sourceDigest))).oracle
          (compileScript
            (Script.done
              (Except.ok { out := out, gamma := gamma, middle := middle' },
                middleDigest') :
              Script Bytes Block
                (Except FSAuthenticatedInterleavedPrefixMiddle.Error
                  (Partial body z) × Block) 0))).oracle.history := middleToDone
    _ =
        (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
          middleFuel sourceRun.oracle
          (compileScript
            (factoredMiddleContinuationAt body z out gamma
              sourceDigest))).oracle.history := by
      rw [middleOracle]
    _ =
        (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel
          v7
          (compileScript
            (factoredPrefixMiddleScript firstWork secondWork z body
              digest))).oracle.history := by
      rw [sourceOracle]
      rfl
    _ <+:
        (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
          (fuel -
            (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
              fuel v7
              (compileScript
                (factoredPrefixMiddleScript firstWork secondWork z body
                  digest))).steps)
          (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
            fuel v7
            (compileScript
              (factoredPrefixMiddleScript firstWork secondWork z body
                digest))).oracle
          (compileScript
            (suffixContinuation cuts body z middleDigest staged))).oracle.history :=
      prefixToSuffix
    _ =
        (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel
          v7
          (compileScript
            (factoredWholeStagedScript firstWork secondWork z cuts body
              digest))).oracle.history := by
      rw [wholeOracle]

#print axioms programmed_postAlpha_history_prefix_factored_whole

end
end AspisV8Completion.FSV8ProgrammedPostAlphaHistoryPrefix
