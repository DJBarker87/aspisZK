import Hir_LifetimeNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_LifetimeBinding
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_WriterSelect Hir_LifetimeExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound

theorem binding_or_collision {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (initial : Store) (schedule : Schedule A (Call A)) (Q0 Q1 : Nat)
    (scheduledBound : ∀ H, (eval H (Hir_Schedule.program native1 copy allocator id c hashv initial schedule)).1.length ≤ Q0+Q1)
    (project : Execution A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) (H : Bytes → State) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
      (eval H (Hir_LifetimeJoint.program c hashv native1 copy allocator id initial schedule project)) ∨
      let selected := Hir_LifetimeExperiment.select c native1 copy allocator id
        (eval H (Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule)).2
      R9PoolRuntimeBinding.P2Prime H selected.1 selected.2 := by
  have result := Hiq_JointBinding.binding_or_collision SelectedTranscriptParams.params.iv
    (Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule) project
    (Hir_LifetimeExperiment.select c native1 copy allocator id) (Q0+Q1+1921)
    (Hir_LifetimeJoint.source_budget c hashv native1 copy allocator id initial schedule Q0 Q1 scheduledBound) H
  rcases result with bad | good
  · left
    simpa only [Hir_LifetimeJoint.program,Hiq_RecordedJoint.evaluation,BinRawByteCollisionTargets.event,
      show Q0+Q1+1921+1044 = Q0+Q1+2965 by omega] using bad
  · exact Or.inr good

#print axioms binding_or_collision
end AspisR1.Hir_LifetimeBinding
end
