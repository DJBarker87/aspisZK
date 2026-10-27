import RPt_BEl_OriginalReference
import RPt_RPx_Transport
import RPt_RPx_AccountCharge
import RPt_ARQ_Join
import RPz8_F3Y_InstalledLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_AccountComposition
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment F3T_ByteCarrier

/-- Exactly ARQ's target, without strengthening its guard/event/recorder or
changing the adversary after H is chosen. This remains the named global join. -/
abbrev Join := @ARQ_Join.Target

/-- Source accounting and original-account charge composed conditionally on
EXACTLY the ARQ deliverable. The source prover recorder is not silently equated
with the original account recorder; the last branch names the latter literally. -/
theorem conditional {A C : Type} (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (D : LiteralByteProtocol.Decoder) (words : CanonicalCutEnrichedTranscript.Words)
    (a : Adversary A) (Q0 Q1 : Nat)
    (head : ∀ H : Bytes → State,(eval H a.first).1.length≤Q0)
    (choice : ∀ input saved post final H,(eval H (a.second input saved post final)).1.length≤Q1)
    (join : ARQ_Join.Target (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier D a Q0 Q1) :
    let cfg := FIp_Install.configuration err c r
    RPx_Transport.Claims cfg hashv (submission a) (Q0+Q1) ∧
    (∀ H : Bytes → State,FS.firstReads FS.emptyTable
      (eval H (Hiq_RecordedJoint.program (SCE_Experiment.account cfg hashv copy allocator CPH_Program.verifier a)
        ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier))).1≤Q0+Q1+2965) ∧
    F3T_AccountCharge.mass (SCE_Experiment.account cfg hashv copy allocator CPH_Program.verifier a)
      ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier) (Q0+Q1)≤F3T_Numeric.accountLoss (Q0+Q1) ∧
    (∀ H : Bytes → State,accepted (eval H (SCE_Experiment.account cfg hashv copy allocator CPH_Program.verifier a)).2=true →
      eval H (F3T_Installed.source cfg hashv (input cfg (eval H (submission a)).2))=
        eval H (F3_Model.verifier D (input cfg (eval H (submission a)).2)) ∨
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program (SCE_Experiment.account cfg hashv copy allocator CPH_Program.verifier a)
          ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)))) := by
  let cfg := FIp_Install.configuration err c r
  have queries : ∀ H : Bytes → State,(eval H (submission a)).1.length≤Q0+Q1 := by
    intro H
    rw [SCE_Experiment.submission_eval]
    exact (head H).trans (Nat.le_add_right Q0 Q1)
  have source := RPx_Transport.transport
    (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r)
    hashv D words (submission a) (Q0+Q1) queries
  rw [F3Y_InstalledLaws.configuration] at source
  have original := RPx_AccountCharge.charged cfg.adapter cfg.currentBase cfg.stageBase cfg.finish
    cfg.reserved cfg.query cfg.geometry cfg.boundaries cfg.std hashv copy allocator CPH_Program.verifier
    a.first a.second Q0 Q1 head choice ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)
  exact ⟨source,original.1,original.2,join⟩

#print axioms conditional
end AspisR1.BEl_AccountComposition
end
