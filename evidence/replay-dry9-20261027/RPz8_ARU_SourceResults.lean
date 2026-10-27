import RPz8_ARU_Replies
import RPz8_ARU_WrapperSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_SourceResults
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
theorem accepted {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) :
    (SdkC_Source.run hashv (ARS_NativeAccount.firstSyntax (FIp_Install.configuration err c r) hashv copy allocator
      CPH_Program.verifier (eval H a.first).2) []).1 = ok (.Ok (n.entry.saved,n.entry.post1,n.entry.final1)) ∧
    (SdkC_Source.run hashv (ARS_NativeAccount.secondSyntax (FIp_Install.configuration err c r) hashv allocator
      CPH_Program.verifier (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2) []).1 =
      ok (.Ok (n.entry.post2,n.entry.final2)) := by
  let cfg := FIp_Install.configuration err c r
  have ext : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk cfg.adapter cfg.currentBase cfg.stageBase cfg.finish cfg.reserved
        cfg.query cfg.geometry cfg.boundaries cfg.std) native1 native2 hashv := by
    rw [←ARQ_Installation.dictionary err c r]
    exact extraction
  have firstSource := ARU_WrapperSource.first cfg.adapter cfg.currentBase cfg.stageBase cfg.finish
    cfg.reserved cfg.query cfg.geometry cfg.boundaries cfg.std hashv copy allocator
    (eval H a.first).2.entry CPH_Program.verifier (eval H a.first).2.data (eval H a.first).2.state
    native1 native2 ext n.entry.saved n.entry.post1 n.entry.final1 n.entry.accepted1
  have secondSource := ARU_WrapperSource.second cfg.adapter cfg.currentBase cfg.stageBase cfg.finish
    cfg.reserved cfg.query cfg.geometry cfg.boundaries cfg.std hashv allocator
    (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry CPH_Program.verifier
    (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.data
    (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.slot
    (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.state
    native1 native2 ext n.entry.post2 n.entry.final2 n.entry.accepted2
  exact ⟨firstSource,secondSource⟩

#print axioms accepted
end AspisR1.ARU_SourceResults
end
