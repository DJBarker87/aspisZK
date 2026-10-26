import ART_AccountAccepted
import ARQ_Observer
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_ChargeEquality
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment

/-- On acceptance the exact collision event (including its audit reads), not
just its budget, is unchanged. No interior read deletion is used. -/
theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (H : Bytes → State)
    (yes : SCE_Experiment.accepted (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 = true) :
    eval H (Hiq_RecordedJoint.program (ART_PartialAccount.account c hashv copy allocator id a)
      ARQ_Observer.project (ARQ_Observer.select c id)) =
    eval H (Hiq_RecordedJoint.program (SCE_Experiment.account c hashv copy allocator id a)
      ARQ_Observer.project (ARQ_Observer.select c id)) := by
  simp only [Hiq_RecordedJoint.program,Hist_JointCharge.joint,Hist_AuditQueries.augmented,SdkC_Replay.augmented,AspisV8R19.OracleProgramOps.eval_bind,OracleProgramRecording.eval_record,
    ART_AccountAccepted.exact c hashv copy allocator id a H yes]

#print axioms accepted
end AspisR1.ART_ChargeEquality
end
