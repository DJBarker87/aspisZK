import RPz8_ARW_LocalBudget
import RPz8_ARW_Induced
import RPz8_ARX_LocalCharge
import RPz8_ARQ_Observer
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNC_RecSelect
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment

/-- The adversary remains universally quantified. Only its actual H-world
choices are associated to the deployed occurrences. No TX2 acceptance. -/
theorem selects {A F C : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (cfg : DrvC_Installation.Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk cfg) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (e1 e2 : Entry) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state1 state2 final1 : A) (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 CPH_Program.verifier data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (a : Adversary A) (Q : Nat)
    (queries : ∀ K, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a K).length ≤ Q)
    (r1 : (eval H a.first).2 = ⟨e1,data1,state1⟩)
    (r2 : (eval H (a.second ⟨e1,data1,state1⟩ saved post1 final1)).2 = ⟨e2,data2,slot,state2⟩) :
    ARQ_Observer.select cfg CPH_Program.verifier
      (eval H (ARX_LocalCharge.bounded
        (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a) Q)).2 =
      P2P_NativeSelection.pair (DrvC_Installation.sdk cfg) CPH_Program.verifier e1 e2 data2 slot := by
  have ext : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk cfg.adapter cfg.currentBase cfg.stageBase cfg.finish cfg.reserved
        cfg.query cfg.geometry cfg.boundaries cfg.std) native1 native2 hashv := extraction
  have firstSource := ARU_WrapperSource.first cfg.adapter cfg.currentBase cfg.stageBase cfg.finish
    cfg.reserved cfg.query cfg.geometry cfg.boundaries cfg.std hashv copy allocator e1
    CPH_Program.verifier data1 state1 native1 native2 ext saved post1 final1 accepted1
  have agrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
      (ARS_NativeAccount.firstSyntax cfg hashv copy allocator CPH_Program.verifier
        (eval H a.first).2) []).2 := by
    intro q member digest returned
    have associated := SdkC_Source.associated hashv _ [] (by simp) q member
    exact (syscall.returningValue q.parts digest (associated.symm.trans returned)).trans (p1.realization _)
  have reply : (eval H (ART_PartialAccount.wrapper hashv
      (ARS_NativeAccount.firstSyntax cfg hashv copy allocator CPH_Program.verifier
        (eval H a.first).2))).2 = ok (.Ok (saved,post1,final1)) := by
    rw [ART_WrapperExact.execution hashv H _ agrees]
    rw [r1]
    exact firstSource
  have nativeReply : S2W_D189Wrappers.first native1 copy allocator
      (eval H a.first).2.entry CPH_Program.verifier (eval H a.first).2.data
        (eval H a.first).2.state = ok (.Ok (saved,post1,final1)) := by
    rw [r1]; exact accepted1
  have work : ART_AdversaryWork.work cfg hashv copy allocator CPH_Program.verifier a H ≤ Q := by
    have same : (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length =
        ART_AdversaryWork.work cfg hashv copy allocator CPH_Program.verifier a H := by
      simp only [ARW_Induced.issued,nativeReply,List.length_append,ART_AdversaryWork.work,reply]
    rw [←same]
    exact queries H
  have bound := ARW_LocalBudget.issued cfg hashv copy allocator CPH_Program.verifier a Q H work
  rw [ARX_LocalCharge.exact _ Q H bound]
  unfold ART_PartialAccount.account
  simp only [eval_bind,reply]
  simp only [eval,List.append_nil]
  rw [r1,r2]
  rfl

#print axioms selects
end AspisR1.NNC_RecSelect
