import RPz8_ARU_Cuts
import RPz8_ARQ_BankCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Checkpoint
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
theorem selected {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    (std : S2W_TrustedStd.TrustedStd copy) :
    ∃ f s, SourceCuts (SCH_IdealSdk.dictionary (FIp_Install.configuration err c r) hashv H)
      (eval H a.first).2.entry.first
      ((eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry.second secondSizes)
      n.entry.saved f s ∧
      MultiproofConeCanonical.bytesOf s.checkpoint.val = MultiproofConeCanonical.bytesOf n.entry.saved.val := by
  obtain ⟨f,s,cuts,decoded⟩ := ARU_Cuts.selected L copy allocator c err r native1 native2 hashv extraction a H n
  exact ⟨f,s,cuts,ARQ_BankCut.checkpoint c err r hashv copy std allocator native1 native2 extraction a H
    n.entry.saved n.entry.post1 n.entry.post2 n.entry.final1 n.entry.final2 n.entry.accepted1 n.entry.accepted2
    n.entry.p n.entry.t n.entry.u n.entry.actions n.entry.game n.entry.RuntimePersistence f s cuts⟩

#print axioms selected
end AspisR1.ARU_Checkpoint
end
