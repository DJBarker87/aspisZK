import Hiq_DrvExperiment
import Hiq_BindingFailure
import Hiq_AccountEvent
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DrvRecorded
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

def program (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :=
  Hiq_RecordedJoint.program (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond)
    project (Hiq_ByteSelection.select (sdk c) id)

theorem source_view (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (H : Bytes → State) :
    (eval H (program c hashv copy allocator id adversary chooseSecond project)).2 =
      eval H (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond) :=
  Hiq_RecordedJoint.source_view _ _ _ H

theorem binding_failure_mass (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    lazyMean (program c hashv copy allocator id adversary chooseSecond project) emptyTable
      (fun v => indicator (Hiq_BindingFailure.failure (Hiq_ByteSelection.select (sdk c) id) v)) ≤
      6*((Q0+Q1+2965 : Nat) : Rat)^2/(256^32 : Rat) := by
  have bound := Hiq_BindingFailure.mass (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond)
    project (Hiq_ByteSelection.select (sdk c) id) (Q0+Q1+1921)
    (Hiq_DrvExperiment.source_budget c hashv copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound)
  simpa only [program,show Q0+Q1+1921+1044 = Q0+Q1+2965 by omega] using bound

#print axioms source_view
#print axioms binding_failure_mass
end AspisR1.Hiq_DrvRecorded
end
