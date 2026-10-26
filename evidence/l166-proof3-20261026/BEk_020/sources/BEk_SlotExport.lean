import BEk_CutExport
import BEk_Returning
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_SlotExport
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Exact BEj current-slot export, now fed by the SAME SdkC/ARU Returning
packet at its concrete Prepared/root input. The physical local law is retained. -/
theorem current {S E : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (H : Bytes → State) (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest)
    (state : S) (before : Log) (native : BEh_Scope.Outcome S Unit E)
    (law : BEh_Scope.Law native
      (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv proof p root) state before))
    (returning : SdkC_BatchPair.Returning hashv H (SdkC_BatchSource.currentCode hashv proof p root) (.Ok ())) :
    BEj_SlotExport.Prefix hashv H (SdkC_BatchSource.currentCode hashv proof p root) before native.2.2 :=
  BEk_CutExport.queried call hashv binding H _ 900
    (GExq_BatchBudget.current hashv proof p root) state before native law
    (BEk_Returning.agrees hashv H _ _ returning)

theorem stage {S E : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (H : Bytes → State) (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Digest)
    (state : S) (before : Log) (native : BEh_Scope.Outcome S Unit E)
    (law : BEh_Scope.Law native
      (BEf_Carrier.run call (SdkC_BatchSource.stageCode hashv proof p root) state before))
    (returning : SdkC_BatchPair.Returning hashv H (SdkC_BatchSource.stageCode hashv proof p root) (.Ok ())) :
    BEj_SlotExport.Prefix hashv H (SdkC_BatchSource.stageCode hashv proof p root) before native.2.2 :=
  BEk_CutExport.queried call hashv binding H _ 900
    (GExq_BatchBudget.stage hashv proof p root) state before native law
    (BEk_Returning.agrees hashv H _ _ returning)

#print axioms current
#print axioms stage
end AspisR1.BEk_SlotExport
end
