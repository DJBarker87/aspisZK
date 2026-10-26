import ARU_Replies
import ARS_Chronology
import ARU_WrapperSource
import ARU_OracleLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Factory
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_D189Consolidation
/-- Query-restricted support for an actual native accepted execution. The
original native-world witness is fixed before H; H need not satisfy global P1.
All native/game data remain attached to the actual response-selected entries. -/
theorem deployed {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (consistent : ARS_AccountReplay.Consistent
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H) :
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
  have replies := ARU_Replies.accepted L copy allocator c err r native1 native2 hashv extraction a native n
  have pieces := ARS_Chronology.pieces (FIp_Install.configuration err c r) hashv copy allocator
    CPH_Program.verifier a native H n.entry.saved n.entry.post1 n.entry.final1 replies.1 consistent
  have firstEq := congrArg Prod.snd pieces.1
  have secondEq :
      (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2 =
        (eval native (a.second (eval native a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2 := by
    rw [firstEq]
    exact congrArg Prod.snd pieces.2.2.1
  have same := ARS_AccountReplay.replay _ native H consistent
  let entry : ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a H := {
    saved := n.entry.saved, post1 := n.entry.post1, post2 := n.entry.post2
    final1 := n.entry.final1, final2 := n.entry.final2, w1 := n.entry.w1, w2 := n.entry.w2
    admission1 := by simpa only [firstEq] using n.entry.admission1
    admission2 := by simpa only [secondEq] using n.entry.admission2
    accepted1 := by simpa only [firstEq] using n.entry.accepted1
    accepted2 := by simpa only [secondEq] using n.entry.accepted2
    p := n.entry.p, t := n.entry.t, u := n.entry.u, actions := n.entry.actions
    game := by rw [secondEq,firstEq]; exact n.entry.game
    RuntimePersistence := n.entry.RuntimePersistence }
  let cfg := FIp_Install.configuration err c r
  have ext : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk cfg.adapter cfg.currentBase cfg.stageBase cfg.finish cfg.reserved
        cfg.query cfg.geometry cfg.boundaries cfg.std) native1 native2 hashv := by
    rw [←ARQ_Installation.dictionary err c r]
    exact extraction
  have firstSource := ARU_WrapperSource.first cfg.adapter cfg.currentBase cfg.stageBase cfg.finish
    cfg.reserved cfg.query cfg.geometry cfg.boundaries cfg.std hashv copy allocator
    (eval native a.first).2.entry CPH_Program.verifier (eval native a.first).2.data (eval native a.first).2.state
    native1 native2 ext n.entry.saved n.entry.post1 n.entry.final1 n.entry.accepted1
  have secondSource := ARU_WrapperSource.second cfg.adapter cfg.currentBase cfg.stageBase cfg.finish
    cfg.reserved cfg.query cfg.geometry cfg.boundaries cfg.std hashv allocator
    (eval native (a.second (eval native a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry CPH_Program.verifier
    (eval native (a.second (eval native a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.data
    (eval native (a.second (eval native a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.slot
    (eval native (a.second (eval native a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.state
    native1 native2 ext n.entry.post2 n.entry.final2 n.entry.accepted2
  refine ⟨⟨entry,?_,?_⟩⟩
  · rw [firstEq]
    exact ARU_OracleLog.agrees hashv native H _ _ firstSource n.firstAgrees pieces.2.1
  · change ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
      (ARS_NativeAccount.secondSyntax cfg hashv allocator CPH_Program.verifier
        (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2) []).2
    rw [secondEq]
    exact ARU_OracleLog.agrees hashv native H _ _ secondSource n.secondAgrees pieces.2.2.2

#print axioms deployed
end AspisR1.ARU_Factory
end
