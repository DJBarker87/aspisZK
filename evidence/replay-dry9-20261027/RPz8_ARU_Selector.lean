import RPz8_ARU_CutsOrigin
import RPz8_ARU_SelectorPure
import RPz8_ARQ_Observer
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Selector
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
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (SCH_IdealSdk.dictionary (FIp_Install.configuration err c r) hashv H)
      (eval H a.first).2.entry.first
      ((eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry.second secondSizes)
      n.entry.saved f s)
    (origin : P2P_Origin.Fact (SCH_IdealSdk.dictionary (FIp_Install.configuration err c r) hashv H)
      CPH_Program.verifier
      ((eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry.second secondSizes)
      (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.data
      (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.slot s) :
    ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier
      (eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 =
      Hist_PairExperiment.select ⟨f,s⟩ := by
  have replies := ARU_Replies.accepted L copy allocator c err r native1 native2 hashv extraction a H n
  unfold ARQ_Observer.select
  rw [SCG_Selection.actual _ hashv copy allocator CPH_Program.verifier _ a H
    n.entry.saved n.entry.post1 n.entry.final1 replies.1]
  rw [ARQ_Installation.dictionary err c r,←ARU_SelectorPure.pair _ hashv H]
  exact P2P_NativeSelection.on_cuts _ CPH_Program.verifier _ _ _ _ n.entry.saved f s cuts origin

#print axioms selected
end AspisR1.ARU_Selector
end
