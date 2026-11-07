import NNC_NMFB
import NNC_ActualChoices
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNC_ActualRoot
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment MultiproofConeCanonical S2W_NativeConsolidation FS FS2

/-- Native-cut NMF_B at the exact adaptive H-selected entries. Realizes is
rfl, no test or conditioning; the cut-production obligation remains explicit. -/
theorem actual {A C Ambient X : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (base : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (a : Adversary A) (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record)) (final1 : A)
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator (NNC_ActualChoices.first a H).entry CPH_Program.verifier (NNC_ActualChoices.first a H).data (NNC_ActualChoices.first a H).state =
      ok (.Ok (saved,post1,final1)))
    (Q : Nat)
    (queries : ∀ K, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a K).length ≤ Q)
    (f : FirstCut) (s : SecondCut)
 (cuts : NNC_SourceCuts.Cuts (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) (NNC_ActualChoices.first a H).entry.first ((NNC_ActualChoices.second a H saved post1 final1).entry.second S2W_D189Wrappers.secondSizes) saved f s)
 (origin : P2P_Origin.Fact (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) CPH_Program.verifier ((NNC_ActualChoices.second a H saved post1 final1).entry.second S2W_D189Wrappers.secondSizes) (NNC_ActualChoices.second a H saved post1 final1).data (NNC_ActualChoices.second a H saved post1 final1).slot s)
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
  exact NNC_NMFB.root0_or_rec copy allocator base err reservation native1 native2 hashv
    extraction sha256 H p1 syscall
    (NNC_ActualChoices.first a H).entry (NNC_ActualChoices.second a H saved post1 final1).entry
    (NNC_ActualChoices.first a H).data (NNC_ActualChoices.second a H saved post1 final1).data
    (NNC_ActualChoices.second a H saved post1 final1).slot
    (NNC_ActualChoices.first a H).state (NNC_ActualChoices.second a H saved post1 final1).state
    final1 saved post1 accepted1 a Q queries rfl rfl f s cuts origin writerRoot persisted
    writerHeader d hash world domain oracle records events native

#print axioms actual
end AspisR1.NNC_ActualRoot
