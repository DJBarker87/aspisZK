import ARQ_AccountCharge
import ARQ_AccountView
import SCF_Domination
import SCF_RequiredTransport
import SCE_AccountMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_CleanDomination
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open SCE_Experiment F3T_Experiment F3T_ByteCarrier

theorem pointwise {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (Q0 Q1 : Nat) (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)
    (law : SCF_RequiredTransport.CleanAccountTransport c D hashv copy allocator id a Q0 Q1
      ARQ_Observer.project (ARQ_Observer.select c id)) (H : Bytes → State) :
    F3T_Runtime.runtimeMass (eval H (runtime c hashv copy allocator id a)) ≤
        RawRecordedOracleExtractionMassBin.failureMass
          (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (submission a))))) +
        indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
          (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a)
            ARQ_Observer.project (ARQ_Observer.select c id)))) := by
  have dominate := SCF_Domination.pointwise_of_agreement
    (ARQ_AccountView.physical c hashv copy allocator id a H)
    (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (submission a)))))
    (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
      (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a)
        ARQ_Observer.project (ARQ_Observer.select c id))))
    (by intro accepted clean
        have h := law H accepted clean
            rw [first_projection] at h
        exact h)
  rw [SCE_AccountMass.pointwise,first_projection]
  exact dominate
#print axioms pointwise
end AspisR1.ARQ_CleanDomination
end
