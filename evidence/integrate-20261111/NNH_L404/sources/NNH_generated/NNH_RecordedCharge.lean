import NNH_StateSelect
import F3T_AccountCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_RecordedCharge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment FS FS2

/-- The actual bounded account program runs the universally supplied a-top.
No raw-a query budget, constant adversary or Realizes filter occurs. -/
def source {C : Type} (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (base : DrvC_Installation.Configuration FIo_Install.W C)
 (err : C) (r : NP6_StdModel.Reservation)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (a : Adversary Bool) (Q : Nat) :=
 ARX_LocalCharge.bounded
  (ART_PartialAccount.account (FIp_Install.configuration err base r)
   hashv copy NNE_AbortIndicator.allocator CPH_Program.verifier (NNH_StateNormalize.normalize a)) Q

def recorder {C : Type} (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (base : DrvC_Installation.Configuration FIo_Install.W C)
 (err : C) (r : NP6_StdModel.Reservation)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (a : Adversary Bool) (Q : Nat) :=
 Hiq_RecordedJoint.program (source copy base err r hashv a Q) ARQ_Observer.project
  (ARQ_Observer.select (FIp_Install.configuration err base r) CPH_Program.verifier)

/-- Full-space expectation of E_rec for that very recorder. This is the
single existing accountLoss charge, without conditioning on Realizes.
The remaining G0 obligation is failure inclusion at this SAME recorder. -/
theorem bound {C : Type}
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (base : DrvC_Installation.Configuration FIo_Install.W C)
 (err : C) (r : NP6_StdModel.Reservation)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (a : Adversary Bool) (Q : Nat) :
 lazyMean (recorder copy base err r hashv a Q) emptyTable
  (fun v => AspisV8R19.CausalFirstHitUnionBound.indicator
   (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) v))
 ≤ F3T_Numeric.accountLoss Q := by
 apply F3T_AccountCharge.bound
 intro H
 exact (VerifierCallBudget.firstReads_le_length _ _).trans
  (ARX_LocalCharge.budget _ Q H)
#print axioms bound
end AspisR1.NNH_RecordedCharge
