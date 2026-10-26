import ARU_Replies
import ARS_Chronology
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_BankTransport
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
    Nonempty (ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) =
      eval native (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) ∧
    SCE_Experiment.accepted (eval H
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 = true := by
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
  refine ⟨⟨⟨n.entry.saved,n.entry.post1,n.entry.post2,n.entry.final1,n.entry.final2,n.entry.w1,n.entry.w2,
    ?_,?_,?_,?_,n.entry.p,n.entry.t,n.entry.u,n.entry.actions,?_,n.entry.RuntimePersistence⟩⟩,same,?_⟩
  · simpa only [firstEq] using n.entry.admission1
  · simpa only [secondEq] using n.entry.admission2
  · simpa only [firstEq] using n.entry.accepted1
  · simpa only [secondEq] using n.entry.accepted2
  · rw [secondEq,firstEq]
    exact n.entry.game
  · rw [same]
    exact replies.2.2

#print SupportedEntry
#print axioms deployed
end AspisR1.ARU_BankTransport
end
