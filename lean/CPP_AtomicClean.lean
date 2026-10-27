import CPP_AtomicInputs
import Hiq_CleanWorld
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicClean
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_AtomicSchedule Hir_LifetimeExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Non-vacuity of the same measured bad-event/binding experiment. This does
NOT assert a joint accepted native/cryptographic/runtime inhabitant. -/
theorem exists_clean {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (initial : Store) (schedule : Schedule A (Call A))
    (scheduledBound : ∀ H, (eval H (CPP_AtomicSchedule.program native1 copy allocator id c hashv initial schedule)).1.length ≤ 1018)
    (project : Execution A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    ∃ H : Bytes → State,
      ¬ BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv 2965
        (eval H (CPP_AtomicJoint.program c hashv native1 copy allocator id initial schedule project)) ∧
      let selected := Hir_LifetimeExperiment.select c native1 copy allocator id
        (eval H (CPP_AtomicLifetime.program c hashv native1 copy allocator id initial schedule)).2
      R9PoolRuntimeBinding.P2Prime H selected.1 selected.2 := by
  have bound := CPP_AtomicJoint.one_loss c hashv native1 copy allocator id initial schedule 0 0 scheduledBound project
  have small : 6*(2965:Rat)^2/(2:Rat)^256 < 1 := by norm_num
  obtain ⟨H,clean⟩ := Hiq_CleanWorld.exists_clean _ _ (lt_of_le_of_lt bound small)
  refine ⟨H,clean,?_⟩
  rcases CPP_AtomicBinding.binding_or_collision c hashv native1 copy allocator id initial schedule 0 0 scheduledBound project H with bad | good
  · exact False.elim (clean bad)
  · exact good

#print axioms exists_clean
end AspisR1.CPP_AtomicClean
end
