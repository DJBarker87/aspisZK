import Hir_NoUnwrittenAcceptance
import Hir_IdealLifetime
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_IdealJoint
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_LifetimeExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (initial : Store) (schedule : Schedule A (Call A))
    (project : Execution A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))

def program := Hiq_RecordedJoint.program (Hir_IdealLifetime.program c hashv native1 copy allocator id initial schedule)
  project (Hir_LifetimeExperiment.select c native1 copy allocator id)

theorem exact (total : ∀ parts, ∃ digest, hashv parts = .ok digest) :
    program c hashv native1 copy allocator id initial schedule project =
      Hir_SelectedJoint.program c hashv native1 copy allocator id initial schedule project := by
  simp only [program,Hir_SelectedJoint.program,
    Hir_IdealLifetime.total_instance c hashv native1 copy allocator id total initial schedule]

theorem one_loss (total : ∀ parts, ∃ digest, hashv parts = .ok digest) (Q0 Q1 : Nat)
    (scheduledBound : ∀ H, (eval H (Hir_Schedule.program native1 copy allocator id c hashv initial schedule)).1.length ≤ Q0+Q1+1018) :
    lazyMean (program c hashv native1 copy allocator id initial schedule project) emptyTable
      (fun v => indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) v)) ≤
      6*((Q0+Q1+2965 : Nat) : Rat)^2/(2:Rat)^256 := by
  rw [exact c hashv native1 copy allocator id initial schedule project total]
  exact Hir_SelectedJoint.one_loss c hashv native1 copy allocator id initial schedule Q0 Q1 scheduledBound project

#print axioms exact
#print axioms one_loss
end AspisR1.Hir_IdealJoint
end
