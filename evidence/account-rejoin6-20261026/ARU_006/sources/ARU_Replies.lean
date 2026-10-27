import ARU_Support
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Replies
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
    (eval H (SCE_Execution.firstCode (FIp_Install.configuration err c r) hashv copy allocator
      CPH_Program.verifier (eval H a.first).2)).2 = ok (.Ok (n.entry.saved,n.entry.post1,n.entry.final1)) ∧
    (eval H (SCE_Execution.secondCode (FIp_Install.configuration err c r) hashv allocator
      CPH_Program.verifier (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2)).2 =
      ok (.Ok (n.entry.post2,n.entry.final2)) ∧
    accepted (eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 = true := by
  exact ARU_NativeReplies.accepted c err r hashv copy allocator native1 native2 extraction H a
    CPH_Program.verifier n.entry.saved n.entry.post1 n.entry.post2 n.entry.final1 n.entry.final2
    n.firstAgrees n.secondAgrees n.entry.accepted1 n.entry.accepted2

#print axioms accepted
end AspisR1.ARU_Replies
end
