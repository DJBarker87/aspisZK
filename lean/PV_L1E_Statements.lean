import PV_L1E_CallbackSafety
import PV_L1E_CountSkeleton
import PV_L1E_EntryOrder
import PV_L1E_ErasureObstruction
import PV_L1E_OriginalCountSkeleton
import PV_L1E_OriginalSourceCount
import PV_L1E_OwnerJoin
import PV_L1E_QuerySafety
import PV_L1E_RetrySource
import PV_L1E_SafeObserve
import PV_L1E_SafetyTactics
import PV_L1E_SourceEntries
import PV_L1E_SourceOwnerLinks
import PV_L1E_Source_070
set_option autoImplicit false
namespace PV_L1E_Statements
open PV_RJ4IDB
open PV_L1E_CountSkeleton PV_L1E_OriginalCountSkeleton
/-- Combined conditional COUNT input and the existing lossless native decoder.
The original four source/world links remain explicit and uninstantiated. -/
theorem combined {I A S P : Type} (actualCount : I → List Nat × List Nat)
    (native : I → NativeTrace A) (sourceWorld bodyWorld : I → Trace A)
    (owner : I → R1Z.SideChannelL1AttemptRecord.Owner S P)
    (initial : I → S) (fuel index : I → Nat)
    (adapt : I → R1Z.SideChannelL1AttemptRecord.Run P × S → Trace A)
    (acquisition : PV_L1E_Link_CountAcquisition actualCount sourceWorld)
    (body : PV_L1E_Link_BodyWrapper sourceWorld bodyWorld)
    (retry : PV_L1E_Link_OriginalRetry bodyWorld owner initial fuel index adapt)
    (coupling : PV_L1E_Link_NativeD163 native owner initial fuel index adapt) :
    PV_RJ4IDB.OpenInputs.L1_COUNT_TRACE actualCount native ∧
      ∀ i, nativeObservation (native i) = decoder (modelTrace (native i)) :=
  ⟨original_count_trace actualCount native sourceWorld bodyWorld owner initial fuel index adapt
      acquisition body retry coupling,PV_RJ4IDB.all_prefixes native⟩
#print combined
#print axioms combined
end PV_L1E_Statements
#check PV_L1E_CallbackSafety.safe_coe
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_030
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_003
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_004
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_005
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_006
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_007
#check PV_L1E_CallbackSafety.safe_PV_L1D_QueryAbsorb
#check PV_L1E_CallbackSafety.safe_PV_L1D_QueryProducer
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_008
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_009
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_015
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_017
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_018
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_019
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_020
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_021
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_023
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_024
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_025
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_026
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_027
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_031
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_033
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_037
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_038
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_039
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_041
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_042
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_043
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_044
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_045
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_046
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_047
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_049
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_051
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_052
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_053
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_054
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_055
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_056
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_058
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_062
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_063
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_065
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_066
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_067
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_068
#check PV_L1E_CallbackSafety.safe_PV_L1D_Source_069
#check PV_L1E_CallbackSafety.safe_PV_L1E_Source_070
#check PV_L1E_CountSkeleton.count_trace
#check PV_L1E_EntryOrder.entryRange_length
#check PV_L1E_EntryOrder.all_outcomes
#check PV_L1E_ErasureObstruction.result_erasure_does_not_determine_entries
#check PV_L1E_ErasureObstruction.outer_failure_not_total_owner
#check PV_L1E_ErasureObstruction.native_output_does_not_determine_count
#check PV_L1E_OriginalCountSkeleton.original_count_trace
#check PV_L1E_OriginalSourceCount.same_original_success
#check PV_L1E_OwnerJoin.original_run
#check PV_L1E_OwnerJoin.original_prefix
#check PV_L1E_OwnerJoin.run_of_link
#check PV_L1E_QuerySafety.safe_coe
#check PV_L1E_QuerySafety.safe_PV_L1D_QueryAbsorb
#check PV_L1E_RetrySource.attempt_erasure
#check PV_L1E_RetrySource.run_erasure
#check PV_L1E_RetrySource.complete_source
#check PV_L1E_RetrySource.client_no_final_rejected
#check PV_L1E_SafeObserve.query
#check PV_L1E_SafeObserve.phase
#check PV_L1E_SourceEntries.callback_bind
#check PV_L1E_SourceEntries.attempt_entries
#check PV_L1E_SourceEntries.successful_callbacks
#check PV_L1E_SourceEntries.all_outcomes
#check PV_L1E_SourceOwnerLinks.source_owner
#check PV_L1E_Source_070.complete_result
#print PV_L1E_CountSkeleton.PV_L1E_Link_CountAcquisition
#print PV_L1E_CountSkeleton.PV_L1E_Link_BodyWrapper
#print PV_L1E_CountSkeleton.PV_L1E_Link_RetryJoin
#print PV_L1E_CountSkeleton.PV_L1E_Link_NativeOriginal
#print PV_L1E_OriginalCountSkeleton.PV_L1E_Link_OriginalRetry
#print PV_L1E_OriginalCountSkeleton.PV_L1E_Link_NativeD163
#print PV_L1E_OwnerJoin.PV_L1E_Link_SourceOwner
#print PV_L1E_SourceOwnerLinks.PV_L1E_Link_OwnerControl
#print PV_L1E_SourceOwnerLinks.PV_L1E_Link_OwnerEvents
#check PV_RJ4IDB.OpenInputs.L1_COUNT_TRACE
#check PV_RJ4IDB.OpenInputs.L1_ORACLE_PREFIX
#check PV_RJ4IDB.OpenInputs.L1_TIME_TRACE
#check PV_RJ4IDB.OpenInputs.L1_RETAINED_SIDECHANNELS
