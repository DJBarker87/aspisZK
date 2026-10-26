import ARU_Selector
import ARU_ByteMatch
import ARQ_BankCut
import SCH_DriverAcceptance
import SCH_DecodeAlign
import P2P_Charge
import RawJ_CollisionBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_SourceAlternative
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
theorem accepted {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    (std : S2W_TrustedStd.TrustedStd copy)
    (Q0 Q1 : Nat) (prefixBound : ∀ K, (eval K a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final K, (eval K (a.second i saved post final)).1.length ≤ Q1) :
    (eval H (F3T_Installed.source (FIp_Install.configuration err c r) hashv
      (F3T_ByteCarrier.input (FIp_Install.configuration err c r) (eval H (submission a)).2))).2 = true ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
      (eval H (Hiq_RecordedJoint.program
        (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
        ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier))) := by
  let cfg := FIp_Install.configuration err c r
  obtain ⟨f,s,cuts,decoded,origin⟩ := ARU_CutsOrigin.selected L copy allocator c err r native1 native2 hashv extraction a H n
  have selector := ARU_Selector.selected L copy allocator c err r native1 native2 hashv extraction a H n f s cuts origin
  have checkpoint := ARQ_BankCut.checkpoint c err r hashv copy std allocator native1 native2 extraction a H
    n.entry.saved n.entry.post1 n.entry.post2 n.entry.final1 n.entry.final2 n.entry.accepted1 n.entry.accepted2
    n.entry.p n.entry.t n.entry.u n.entry.actions n.entry.game n.entry.RuntimePersistence f s cuts
  have alternative := P2P_Charge.binding_or_collision
    (account cfg hashv copy allocator CPH_Program.verifier a) ARQ_Observer.project
    (ARQ_Observer.select cfg CPH_Program.verifier) (Q0+Q1)
    (RawJ_CollisionBudget.first_reads cfg.adapter cfg.currentBase cfg.stageBase cfg.finish cfg.reserved
      cfg.query cfg.geometry cfg.boundaries cfg.std hashv copy allocator CPH_Program.verifier
      a.first a.second Q0 Q1 prefixBound choiceBound) H
  rcases alternative with bad | binding
  · exact Or.inr bad
  · rw [selector] at binding
    have matched := ARU_ByteMatch.digest_matches cfg hashv H _ _ n.entry.saved f s cuts checkpoint
    obtain ⟨proof,pub⟩ := binding matched
    have decoded' : Port1_Driver.decodeSemantic (DrvC_Installation.sdk cfg) f.pub = ok (some f.semantic) := by
      rw [←SCH_DecodeAlign.installed (FIp_Install.select r c) err r hashv H]
      exact decoded
    have source := SCH_DriverAcceptance.accepted (FIp_Install.select r c) err r hashv H
      _ _ n.entry.saved f s cuts decoded' proof pub checkpoint
    have bytes := SCE_FirstCutBytes.submitted_cut (eval H a.first).2 _ _ n.entry.saved f s cuts
    have submitted : (eval H (submission a)).2 =
        (⟨MultiproofConeCanonical.bytesOf f.pub.val,MultiproofConeCanonical.bytesOf f.proof.val⟩ : F3T_ByteCarrier.Submission) := by
      rw [submission_eval]
      exact SCE_SubmissionExt.equal _ _ bytes.1 bytes.2
    exact Or.inl (by rw [submitted]; exact source)

#print axioms accepted
end AspisR1.ARU_SourceAlternative
end
