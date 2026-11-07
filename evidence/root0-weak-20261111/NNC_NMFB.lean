import NNC_RecRoot
import NNC_RecSelect
import RPz8_ARW_LocalBudget
import RPz8_ARW_Induced
import RPz8_ARX_LocalCharge
import RPz8_ARQ_Observer
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNC_NMFB
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment MultiproofConeCanonical S2W_NativeConsolidation FS FS2

/-- E_rec is literally the event already charged by FJp_Mass. The native
selected-cut production is explicit, not asserted to follow from Realizes. -/
theorem root0_or_rec {A C Ambient X : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (base : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (e1 e2 : Entry) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state1 state2 final1 : A) (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 CPH_Program.verifier data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (a : Adversary A) (Q : Nat)
    (queries : ∀ K, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a K).length ≤ Q)
    (r1 : (eval H a.first).2 = ⟨e1,data1,state1⟩)
    (r2 : (eval H (a.second ⟨e1,data1,state1⟩ saved post1 final1)).2 = ⟨e2,data2,slot,state2⟩)
    (f : FirstCut) (s : SecondCut)
 (cuts : NNC_SourceCuts.Cuts (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) e1.first (e2.second S2W_D189Wrappers.secondSizes) saved f s)
 (origin : P2P_Origin.Fact (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) CPH_Program.verifier (e2.second S2W_D189Wrappers.secondSizes) data2 slot s)
 (writerRoot : NLP_InputDomain.Root0 saved.deref f.proof)
 (persisted : bytesOf s.checkpoint.val=bytesOf saved.val)
 (writerHeader : NLW_ReaderHeader.decode (bytesOf saved.val)=
  some (H (bytesOf f.proof.val),H (bytesOf f.pub.val)))
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
 (world : NLM_PacketTypes.World Ambient)
 (domain : NNC_064Weak.Domain (NLW_Full064.Args.mk d s.pub s.proof s.checkpoint hash))
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest d) hash H)
 (records : List (NLT_NativeInvocation.Occurrence H d hash))
 (events : List (NLW_Full064.Event Ambient X))
 (native : NMN_064.Native H ⟨⟨d,s.pub,s.proof,s.checkpoint,hash⟩,world⟩
  (.common (.resolved (ok (.Ok ())) records)) events)
 :
    (NLP_InputDomain.Root0 s.checkpoint s.proof ∧
      NLT_CompleteRoot.RowSpec H d s.pub s.proof s.checkpoint hash) ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program
        (ARX_LocalCharge.bounded (ART_PartialAccount.account (FIp_Install.configuration err base reservation)
          hashv copy allocator CPH_Program.verifier a) Q)
        ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err base reservation) CPH_Program.verifier))) := by
  let cfg := (FIp_Install.configuration err base reservation)
  let source := ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a
  have sel := NNC_RecSelect.selects copy allocator base err reservation native1 native2 hashv
    extraction sha256 H p1 syscall e1 e2 data1 data2 slot state1 state2 final1 saved post1
    accepted1 a Q queries r1 r2
  exact NNC_RecRoot.root0_or_rec_collision (ARX_LocalCharge.bounded source Q) ARQ_Observer.project
    (ARQ_Observer.select cfg CPH_Program.verifier) Q
    (fun K => (VerifierCallBudget.firstReads_le_length _ _).trans (ARX_LocalCharge.budget source Q K))
    H (DrvC_Installation.sdk cfg) CPH_Program.verifier e1 e2 data2 slot saved f s cuts origin
    writerRoot persisted writerHeader d hash world domain oracle records events native sel

#print axioms root0_or_rec
end AspisR1.NNC_NMFB
