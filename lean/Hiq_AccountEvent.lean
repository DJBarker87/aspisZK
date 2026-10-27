import Hiq_CanonicalEvent
import Hiq_DrvExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_AccountEvent
open Aeneas Aeneas.Std Result GExq_AccountExperiment S2Trust S2W_D189Entry S2W_D189Wrappers
open FS FS2 FS2.Duplex DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {A F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A))

theorem canonical_to_joint (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (H : Bytes → State)
    (hit : AuS1_Finish.Collision H
      (eval H (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond)).1
      (project (eval H (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond)).2).1
      (project (eval H (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond)).2).2) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
      (eval H (Hiq_DrvExperiment.joint c hashv copy allocator id adversary chooseSecond project)) := by
  have included := Hiq_CanonicalEvent.source_to_joint
    (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond) project (Hiq_ByteSelection.select (sdk c) id)
    (Q0+Q1+1921) (Hiq_DrvExperiment.source_budget c hashv copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound) H hit
  simpa only [Hiq_DrvExperiment.joint,show Q0+Q1+1921+1044 = Q0+Q1+2965 by omega] using included

#print axioms canonical_to_joint
end AspisR1.Hiq_AccountEvent
end
