import RPt_BEl_PrefixRecorder
import RPt_BEl_SlotObservation
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_LocalCut
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Observe a fresh private reference recorder at an arbitrary pre-existing
backend state. Prefix concatenation is performed after the local cut. -/
def fresh {S E : Type} (call : Parts → S → Result Digest × S)
    (code : Code (core.result.Result Unit E)) (state : S) :=
  BEl_PartialRecorder.observation (BEl_PartialRecorder.run call code state [])

theorem append {S E : Type} (call : Parts → S → Result Digest × S)
    (code : Code (core.result.Result Unit E)) (state : S) (before : Log) :
    (BEl_SlotObservation.observe call code state before).2.2 =
      before ++ (fresh call code state).2.2 := by
  exact congrArg (fun out => out.2.2)
    (BEl_PrefixRecorder.observation_prefix call code state before)

/-- Reference packet with the caller-owned local log appended at its recorder
cut. The physical shipped-body bridge is still required before deployment use. -/
theorem current {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1=hashv parts)
    (H : Bytes → State) (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest)
    (state : S) (before : Log)
    (returning : SdkC_BatchPair.Returning hashv H (SdkC_BatchSource.currentCode hashv proof p root) (.Ok ())) :
    BEj_SlotExport.Prefix hashv H (SdkC_BatchSource.currentCode hashv proof p root) before
      (before ++ (fresh call (BEl_ReferenceSource.currentCode hashv proof p root) state).2.2) := by
  rw [←append call (BEl_ReferenceSource.currentCode hashv proof p root) state before]
  exact BEl_SlotObservation.current_prefix call hashv binding H proof p root state before returning

theorem stage {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1=hashv parts)
    (H : Bytes → State) (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Digest)
    (state : S) (before : Log)
    (returning : SdkC_BatchPair.Returning hashv H (SdkC_BatchSource.stageCode hashv proof p root) (.Ok ())) :
    BEj_SlotExport.Prefix hashv H (SdkC_BatchSource.stageCode hashv proof p root) before
      (before ++ (fresh call (BEl_ReferenceSource.stageCode hashv proof p root) state).2.2) := by
  rw [←append call (BEl_ReferenceSource.stageCode hashv proof p root) state before]
  exact BEl_SlotObservation.stage_prefix call hashv binding H proof p root state before returning

#print axioms append
#print axioms current
#print axioms stage
end AspisR1.BEl_LocalCut
end
