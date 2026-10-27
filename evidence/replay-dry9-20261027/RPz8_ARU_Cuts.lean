import RPz8_ARU_Replies
import RPz8_SCH_SourceFirst
import RPz8_SCH_SourceSecond
import RPz8_SCH_DecodedCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Cuts
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
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) :
    ∃ f s, SourceCuts (SCH_IdealSdk.dictionary (FIp_Install.configuration err c r) hashv H)
      (eval H a.first).2.entry.first
      ((eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry.second secondSizes)
      n.entry.saved f s ∧
      Port1_Driver.decodeSemantic (SCH_IdealSdk.dictionary (FIp_Install.configuration err c r) hashv H) f.pub =
        ok (some f.semantic) := by
  have replies := ARU_Replies.accepted L copy allocator c err r native1 native2 hashv extraction a H n
  exact SCH_DecodedCuts.pair _ CPH_Program.verifier _ _ _ _ _ n.entry.saved
    (SCH_SourceFirst.accepted _ hashv copy allocator CPH_Program.verifier _ n.entry.saved n.entry.post1 n.entry.final1 H replies.1)
    (SCH_SourceSecond.accepted _ hashv allocator CPH_Program.verifier _ n.entry.post2 n.entry.final2 H replies.2.1)

#print axioms selected
end AspisR1.ARU_Cuts
end
