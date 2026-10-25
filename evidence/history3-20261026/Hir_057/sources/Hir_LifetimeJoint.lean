import Hir_LifetimeBudget
import Hiq_AccountLoss
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_LifetimeJoint
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_WriterSelect Hir_LifetimeExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (initial : Store) (schedule : Schedule A (Call A))

def program (project : Execution A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :=
  Hiq_RecordedJoint.program (Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule)
    project (Hir_LifetimeExperiment.select c native1 copy allocator id)

theorem source_budget (Q0 Q1 : Nat)
    (scheduledBound : ∀ H, (eval H (Hir_Schedule.program native1 copy allocator id c hashv initial schedule)).1.length ≤ Q0+Q1)
    (H : Bytes → State) :
    firstReads emptyTable (eval H (Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule)).1 ≤ Q0+Q1+1921 :=
  (VerifierCallBudget.firstReads_le_length _ _).trans
    (Hir_LifetimeBudget.source c hashv native1 copy allocator id initial schedule Q0 Q1 scheduledBound H)

/-- ONE collision charge covers canonical1040 replay plus all FOUR selected
full proof/public reads. The scheduler already contains intervening calls. -/
theorem one_loss (Q0 Q1 : Nat)
    (scheduledBound : ∀ H, (eval H (Hir_Schedule.program native1 copy allocator id c hashv initial schedule)).1.length ≤ Q0+Q1)
    (project : Execution A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    lazyMean (program c hashv native1 copy allocator id initial schedule project) emptyTable
      (fun v => indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) v)) ≤
      6*((Q0+Q1+2965 : Nat) : Rat)^2/(2:Rat)^256 := by
  have bound := Hiq_RecordedBudget.collision
    (Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule)
    project (Hir_LifetimeExperiment.select c native1 copy allocator id) (Q0+Q1+1921)
    (source_budget c hashv native1 copy allocator id initial schedule Q0 Q1 scheduledBound)
  rw [Hiq_Numeric.account_replay (Q0+Q1)] at bound
  simpa only [program,Hiq_Numeric.accountLoss,show Q0+Q1+1921+1044 = Q0+Q1+2965 by omega] using bound

#print axioms source_budget
#print axioms one_loss
end AspisR1.Hir_LifetimeJoint
end
