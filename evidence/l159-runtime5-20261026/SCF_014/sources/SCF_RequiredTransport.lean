import SCF_Domination
import SCE_AccountMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCF_RequiredTransport
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier

/-- An UNPROVED obligation, not an adopted trust item or a premise of any
new deployed theorem. Its quantifier ranges over the SAME oracle and adaptive
adversary in both experiments. This is the exact boundary at which work stops
rather than installing an unapproved source-refinement hypothesis. -/
def CleanAccountTransport {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (Q0 Q1 : Nat)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : GExq_AccountExperiment.Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) : Prop :=
  ∀ H : Bytes → State,
    let v := eval H (account c hashv copy allocator id a)
    let physical := view (v.1,(F3T_Canon.canonInput (input c (submitted v.2.1)),accepted v.2))
    let model := eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (submission a))))
    physical.2.2 = true →
    ¬ BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
      (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a) project select)) →
    model.2.2 = true ∧ OraclePortRefineJoin.RecoveredInputAgreement physical model

#print CleanAccountTransport
end AspisR1.SCF_RequiredTransport
end
