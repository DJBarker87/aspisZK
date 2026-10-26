import ARV_Adaptive
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_AdaptiveOriginal
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw GExq_AccountExperiment SCE_Experiment

theorem original {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (a : Adversary A) (H : Bytes → State) (address : Bytes)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) :
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv
      (ARV_Adaptive.adversary (eval H a.first).2
        (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2 address (H address)) H) := by
  exact ⟨⟨{
    saved := n.entry.saved, post1 := n.entry.post1, post2 := n.entry.post2
    final1 := n.entry.final1, final2 := n.entry.final2, w1 := n.entry.w1, w2 := n.entry.w2
    admission1 := by simpa only [ARV_Adaptive.adversary,eval,if_pos rfl,ite_true] using n.entry.admission1, admission2 := by simpa only [ARV_Adaptive.adversary,eval,if_pos rfl,ite_true] using n.entry.admission2
    accepted1 := by simpa only [ARV_Adaptive.adversary,eval,if_pos rfl,ite_true] using n.entry.accepted1, accepted2 := by simpa only [ARV_Adaptive.adversary,eval,if_pos rfl,ite_true] using n.entry.accepted2
    p := n.entry.p, t := n.entry.t, u := n.entry.u, actions := n.entry.actions
    game := by simpa only [ARV_Adaptive.adversary,eval,if_pos rfl,ite_true] using n.entry.game, RuntimePersistence := n.entry.RuntimePersistence },
    (by simpa only [ARV_Adaptive.adversary,eval,if_pos rfl,ite_true] using n.firstAgrees),
    (by simpa only [ARV_Adaptive.adversary,eval,if_pos rfl,ite_true] using n.secondAgrees)⟩⟩

#print axioms original
end AspisR1.ARV_AdaptiveOriginal
end
