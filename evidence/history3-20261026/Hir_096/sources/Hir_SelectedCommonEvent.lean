import Hir_ExactMargin
import Hiq_CanonicalEvent
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_SelectedCommonEvent
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_LifetimeExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (initial : Store) (schedule : Schedule A (Call A)) (Q0 Q1 : Nat)
    (scheduledBound : ∀ H, (eval H (Hir_Schedule.program native1 copy allocator id c hashv initial schedule)).1.length ≤ Q0+Q1+1018)
    (project : Execution A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))

local notation "source" => Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule
local notation "selected" => Hir_LifetimeExperiment.select c native1 copy allocator id
local notation "joint" => Hir_SelectedJoint.program c hashv native1 copy allocator id initial schedule project

include scheduledBound

theorem subset (H : Bytes → State)
    (hit : AuS1_Finish.Collision H (eval H source).1 (project (eval H source).2).1 (project (eval H source).2).2 ∨
      Hiq_BindingFailure.failure selected (eval H joint)) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) (eval H joint) := by
  have budget := Hir_SelectedJoint.source_budget c hashv native1 copy allocator id initial schedule Q0 Q1 scheduledBound
  rcases hit with canonical | history
  · have bad := Hiq_CanonicalEvent.source_to_joint source project selected (Q0+Q1+1921) budget H canonical
    simpa only [Hir_SelectedJoint.program,Hiq_RecordedJoint.evaluation,BinRawByteCollisionTargets.event,
      show Q0+Q1+1921+1044 = Q0+Q1+2965 by omega] using bad
  · have bad := Hiq_BindingFailure.subset source project selected (Q0+Q1+1921) budget H history
    simpa only [Hir_SelectedJoint.program,show Q0+Q1+1921+1044 = Q0+Q1+2965 by omega] using bad

#print axioms subset
end AspisR1.Hir_SelectedCommonEvent
end
