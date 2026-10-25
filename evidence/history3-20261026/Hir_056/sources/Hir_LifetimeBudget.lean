import Hir_LifetimeExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_LifetimeBudget
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_WriterSelect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

theorem second (store : Store) (call : Call A) (H : Bytes → State) :
    (eval H (Hir_PartialOracle.program hashv (secondCode c hashv allocator id store call))).1.length ≤ 903 :=
  Hir_PartialPrefix.budget hashv _ 903
    (RawJ_InstalledBudget.second c.adapter c.currentBase (AuS1_Install.base c.stageBase)
      c.finish c.reserved c.query c.geometry c.boundaries c.std hashv allocator _ id call.data call.slot call.state) H

theorem source (initial : Store) (schedule : Schedule A (Call A)) (Q0 Q1 : Nat)
    (scheduledBound : ∀ H, (eval H (Hir_Schedule.program native1 copy allocator id c hashv initial schedule)).1.length ≤ Q0+Q1)
    (H : Bytes → State) :
    (eval H (Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule)).1.length ≤ Q0+Q1+1921 := by
  unfold Hir_LifetimeExperiment.program
  apply (GExq_GlobalBudget.bind_length _ _ H (Q0+Q1) 903 ?_ ?_).trans (by omega)
  · have logs := congrArg (fun v => v.1.length) (Hir_RecordErasure.exact c hashv native1 copy allocator id H initial schedule)
    rw [← logs]
    exact scheduledBound H
  · intro recorded
    apply (GExq_GlobalBudget.bind_length _ _ H 903 0
      (second c hashv allocator id recorded.1.1 recorded.1.2.2 H) (fun _ => Nat.zero_le _)).trans
    omega

#print axioms second
#print axioms source
end AspisR1.Hir_LifetimeBudget
end
