import RPz8_ARS_Chronology
import RPz8_ARQ_WorldSupport
import RPz8_ARQ_NativeReplies
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_Coverage
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_D189Consolidation

/-- Same-entry native/runtime/game witnesses, with no global oracle witness for H.
This is a derived output. It is not an extra premise at a replacement top. -/
structure SupportedEntry {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A) (H : Bytes → State) where
  saved : alloc.vec.Vec U8
  post1 : Heap (Nat → Record)
  post2 : Heap (Nat → Record)
  final1 : A
  final2 : A
  w1 : W
  w2 : W
  admission1 : RuntimeEntrypointAdmission L (eval H a.first).2.entry w1 3
  admission2 : RuntimeEntrypointAdmission L
    (eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry w2 7
  accepted1 : first native1 copy allocator (eval H a.first).2.entry CPH_Program.verifier
    (eval H a.first).2.data (eval H a.first).2.state = ok (.Ok (saved,post1,final1))
  accepted2 : let j := (eval H (a.second (eval H a.first).2 saved post1 final1)).2
    second native2 allocator j.entry CPH_Program.verifier j.data j.slot j.state = ok (.Ok (post2,final2))
  p : CPG_Projection.Observations Tx A
  t : Tx
  u : Tx
  actions : List (CPP_BankState.Action A)
  game : CPH_Game.DeployedPairExecution p t u (eval H a.first).2.entry
    (eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry saved actions native1 native2 copy allocator CPH_Program.verifier
  RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
    (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8))
    (CPG_Projection.before p) (CPG_Projection.tentative p) (CPG_Projection.success p) (CPG_Projection.loaded p)


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
    (n : ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (consistent : ARS_AccountReplay.Consistent
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H) :
    Nonempty (SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) =
      eval native (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) ∧
    SCE_Experiment.accepted (eval H
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 = true := by
  have replies := ARQ_NativeReplies.accepted c err r hashv copy allocator native1 native2 extraction
    n.sha256 native n.p1 n.syscall a CPH_Program.verifier n.saved n.post1 n.post2 n.final1 n.final2
    n.accepted1 n.accepted2
  have pieces := ARS_Chronology.pieces (FIp_Install.configuration err c r) hashv copy allocator
    CPH_Program.verifier a native H n.saved n.post1 n.final1 replies.1 consistent
  have firstEq := congrArg Prod.snd pieces.1
  have secondEq :
      (eval H (a.second (eval H a.first).2 n.saved n.post1 n.final1)).2 =
        (eval native (a.second (eval native a.first).2 n.saved n.post1 n.final1)).2 := by
    rw [firstEq]
    exact congrArg Prod.snd pieces.2.2.1
  have same := ARS_AccountReplay.replay _ native H consistent
  refine ⟨⟨⟨n.saved,n.post1,n.post2,n.final1,n.final2,n.w1,n.w2,
    ?_,?_,?_,?_,n.p,n.t,n.u,n.actions,?_,n.RuntimePersistence⟩⟩,same,?_⟩
  · simpa only [firstEq] using n.admission1
  · simpa only [secondEq] using n.admission2
  · simpa only [firstEq] using n.accepted1
  · simpa only [secondEq] using n.accepted2
  · rw [secondEq,firstEq]
    exact n.game
  · rw [same]
    exact replies.2.2

#print SupportedEntry
#print axioms deployed
end AspisR1.ARS_Coverage
end
