import RPt_ARS_AccountDomination
import RPt_ARS_ReachedCharge
import RPt_ARQ_AccountCharge
import RPz8_ARQ_AccountView
import RPz8_SCF_Domination
import RPz8_SCF_RequiredTransport
import RPz8_SCE_AccountMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_ReachedMass
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open SCE_Experiment F3T_Experiment F3T_ByteCarrier
attribute [local irreducible] SCE_Experiment.runtime SCE_Experiment.account
  F3T_Charged.projected Hiq_RecordedJoint.program

/-- CONDITIONAL averaging consumer, never installed as a new deployed top.
The all-world clean law must be PROVED from per-world native/game support;
ARQ_SupportedTransport does so only conditionally on its explicit Supported. -/
theorem bound {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (Q0 Q1 : Nat) (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ARS_ReachedBudget.ChoiceBound c hashv copy allocator id a Q1)
    (law : SCF_RequiredTransport.CleanAccountTransport c D hashv copy allocator id a Q0 Q1
      ARQ_Observer.project (ARQ_Observer.select c id)) :
    F3T_Runtime.deployedFailure (runtime c hashv copy allocator id a) ≤
      lazyMean (F3T_Charged.projected D (F3T_Canon.canon (lift c (submission a)))) FS.emptyTable
        RawRecordedOracleExtractionMassBin.failureMass + F3T_Numeric.accountLoss (Q0+Q1) := by
  have pointwise := fun H => ARS_AccountDomination.pointwise c D hashv copy allocator id a
    Q0 Q1 law H
  have averaged := F3U_Averaging.charge (runtime c hashv copy allocator id a)
    (F3T_Charged.projected D (F3T_Canon.canon (lift c (submission a))))
    (Hiq_RecordedJoint.program (account c hashv copy allocator id a) ARQ_Observer.project (ARQ_Observer.select c id))
    F3T_Runtime.runtimeMass RawRecordedOracleExtractionMassBin.failureMass
    (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)) pointwise
  change F3T_Runtime.deployedFailure (runtime c hashv copy allocator id a) ≤
    lazyMean (F3T_Charged.projected D (F3T_Canon.canon (lift c (submission a)))) FS.emptyTable
      RawRecordedOracleExtractionMassBin.failureMass +
    F3T_AccountCharge.mass (account c hashv copy allocator id a) ARQ_Observer.project
      (ARQ_Observer.select c id) (Q0+Q1) at averaged
  have charged := (ARS_ReachedCharge.charged c hashv copy allocator id a Q0 Q1 prefixBound choiceBound).2.2
  exact le_trans averaged (add_le_add (le_refl _) charged)

#print axioms bound
end AspisR1.ARS_ReachedMass
end
