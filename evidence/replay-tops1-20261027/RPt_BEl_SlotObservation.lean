import RPt_BEl_NativeBatchCut
import RPt_BEk_SlotExport
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_SlotObservation
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def observe {S E : Type} (call : Parts → S → Result Digest × S)
    (code : Code (core.result.Result Unit E)) (state : S) (before : Log) :=
  BEl_PartialRecorder.observation (BEl_PartialRecorder.run call code state (BEl_Recorder.completed before))

theorem current {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest) (state : S) (before : Log) :
    BEh_Scope.Law (observe call (BEl_ReferenceSource.currentCode hashv proof p root) state before)
      (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv proof p root) state before) := by
  unfold observe
  rw [BEl_PartialRecorder.correspondence]
  apply BEl_WeakObservation.law
  exact BEl_ReferenceSource.current call hashv proof p root state before

theorem stage {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : VTop_Stages.verifier.Prepared) (root : Digest) (state : S) (before : Log) :
    BEh_Scope.Law (observe call (BEl_ReferenceSource.stageCode hashv proof p root) state before)
      (BEf_Carrier.run call (SdkC_BatchSource.stageCode hashv proof p root) state before) := by
  unfold observe
  rw [BEl_PartialRecorder.correspondence]
  apply BEl_WeakObservation.law
  exact BEl_ReferenceSource.stage call hashv proof p root state before

/-- The source-computed Returning packet supplies the queried-address export;
no physical/local Law premise is added to this consumer. -/
theorem current_prefix {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (H : Bytes → State) (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest)
    (state : S) (before : Log)
    (returning : SdkC_BatchPair.Returning hashv H (SdkC_BatchSource.currentCode hashv proof p root) (.Ok ())) :
    BEj_SlotExport.Prefix hashv H (SdkC_BatchSource.currentCode hashv proof p root) before
      (observe call (BEl_ReferenceSource.currentCode hashv proof p root) state before).2.2 :=
  BEk_SlotExport.current call hashv binding H proof p root state before _
    (current call hashv proof p root state before) returning

theorem stage_prefix {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (H : Bytes → State) (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Digest)
    (state : S) (before : Log)
    (returning : SdkC_BatchPair.Returning hashv H (SdkC_BatchSource.stageCode hashv proof p root) (.Ok ())) :
    BEj_SlotExport.Prefix hashv H (SdkC_BatchSource.stageCode hashv proof p root) before
      (observe call (BEl_ReferenceSource.stageCode hashv proof p root) state before).2.2 :=
  BEk_SlotExport.stage call hashv binding H proof p root state before _
    (stage call hashv proof p root state before) returning

#print axioms current
#print axioms stage
#print axioms current_prefix
#print axioms stage_prefix
end AspisR1.BEl_SlotObservation
end
