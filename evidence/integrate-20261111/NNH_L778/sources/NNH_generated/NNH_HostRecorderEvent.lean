import NNH_HostExec
import NNC_NMFB
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostRecorderEvent
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NNH_HostCtx NNH_LiteralHost NNH_HostExec
/-- P4 at the literal host: exactly the event in NNC_NMFB.root0_or_rec,
with a-top, the abort-indicator allocator and Q0+Q1. -/
theorem same {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (c : Ctx W Tx) :
 (recSig L copy std).EventRec c ↔
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (c.fixed.Q0+c.fixed.Q1+2965)
  (eval c.sha256 (Hiq_RecordedJoint.program
   (ARX_LocalCharge.bounded (ART_PartialAccount.account (configuration c) (hashv c)
    copy NNE_AbortIndicator.allocator CPH_Program.verifier
    (NNH_StateNormalize.normalize c.fixed.a)) (c.fixed.Q0+c.fixed.Q1))
   ARQ_Observer.project (ARQ_Observer.select (configuration c) CPH_Program.verifier))) := Iff.rfl
#print axioms same
end AspisR1.NNH_HostRecorderEvent
end
