import RPz8_ARU_NativeReplies
import RPz8_ARS_Coverage
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Support
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

/-- Native bank observations plus agreement only at the two issued source logs.
This is a representation obligation, not a new trusted runtime law. -/
structure At {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A) (H : Bytes → State) where
  entry : ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a H
  firstAgrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
    (ARS_NativeAccount.firstSyntax (FIp_Install.configuration err c r) hashv copy allocator
      CPH_Program.verifier (eval H a.first).2) []).2
  secondAgrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
    (ARS_NativeAccount.secondSyntax (FIp_Install.configuration err c r) hashv allocator
      CPH_Program.verifier (eval H (a.second (eval H a.first).2 entry.saved entry.post1 entry.final1)).2) []).2

#print At
end AspisR1.ARU_Support
end
