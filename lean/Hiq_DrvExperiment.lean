import Hiq_AccountBinding
import DrvC_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DrvExperiment
open Aeneas Aeneas.Std Result GExq_AccountExperiment S2Trust S2W_D189Entry S2W_D189Wrappers
open FS FS2 FS2.Duplex DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound

variable {A F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A))

def source : Program Bytes State (GExq_AccountExperiment.Outcome A) :=
  program c.adapter c.currentBase (AuS1_Install.base c.stageBase) c.finish c.reserved c.query c.geometry
    c.boundaries c.std hashv copy allocator id adversary chooseSecond

def joint (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :=
  Hist_JointCharge.joint (source c hashv copy allocator id adversary chooseSecond) project (Hiq_ByteSelection.select (sdk c) id)

theorem source_budget (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)
    (H : Bytes → State) :
    firstReads emptyTable (eval H (source c hashv copy allocator id adversary chooseSecond)).1 ≤ Q0+Q1+1921 :=
  RawJ_CollisionBudget.first_reads c.adapter c.currentBase (AuS1_Install.base c.stageBase) c.finish c.reserved c.query c.geometry
    c.boundaries c.std hashv copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound H

theorem joint_budget (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (H : Bytes → State) :
    firstReads emptyTable (eval H (joint c hashv copy allocator id adversary chooseSecond project)).1 ≤ Q0+Q1+2965 :=
  Hiq_AccountAudit.queries c.adapter c.currentBase (AuS1_Install.base c.stageBase) c.finish c.reserved c.query c.geometry
    c.boundaries c.std hashv copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound project _ H

theorem collision (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    lazyMean (joint c hashv copy allocator id adversary chooseSecond project) emptyTable
      (fun view => indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) view)) ≤
      6*((Q0+Q1+2965 : Nat) : Rat)^2/(256^32 : Rat) :=
  BinRawByteCollisionTargets.mass _ _ _ (joint_budget c hashv copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound project)

theorem result (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (H : Bytes → State) :
    (eval H (joint c hashv copy allocator id adversary chooseSecond project)).2 =
      (eval H (source c hashv copy allocator id adversary chooseSecond)).2 :=
  Hist_JointCharge.same_result H _ _ _

#print axioms source_budget
#print axioms joint_budget
#print axioms collision
#print axioms result
end AspisR1.Hiq_DrvExperiment
end
