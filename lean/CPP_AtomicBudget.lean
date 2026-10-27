import CPP_AtomicLifetime
import Hir_SelectedBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicBudget
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_AtomicSchedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem source {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (initial : Store) (schedule : Schedule A (Call A)) (Q0 Q1 : Nat)
    (bound : ∀ H, (eval H (CPP_AtomicSchedule.program n1 copy allocator id c hashv initial schedule)).1.length ≤ Q0+Q1+1018)
    (H : Bytes → State) :
    (eval H (CPP_AtomicLifetime.program c hashv n1 copy allocator id initial schedule)).1.length ≤ Q0+Q1+1921 := by
  unfold CPP_AtomicLifetime.program
  apply (GExq_GlobalBudget.bind_length _ _ H (Q0+Q1+1018) 903 ?_ ?_).trans (by omega)
  · have logs := congrArg (fun v => v.1.length)
      (CPP_AtomicRecordErasure.exact c hashv n1 copy allocator id H initial schedule)
    rw [← logs]
    exact bound H
  · intro recorded
    apply (GExq_GlobalBudget.bind_length _ _ H 903 0
      (Hir_LifetimeBudget.second c hashv allocator id recorded.1.1 recorded.1.2.2 H) (fun _ => Nat.zero_le _)).trans
    omega

#print axioms source
end AspisR1.CPP_AtomicBudget
end
