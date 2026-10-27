import RPz7_Hir_ScheduleOrigin
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_GenesisOrigin
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem selected_writer {A B : Type}
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (store : Store) (schedule : Schedule A B) (key : Nat)
    (genesis : ∀ key, (store key).owner = id → ¬ Initialized (store key).data)
    (allowed : admissible native1 native2 copy allocator id H store schedule)
    (owner : ((run native1 native2 copy allocator id H store schedule).1 key).owner = id)
    (marker : Initialized ((run native1 native2 copy allocator id H store schedule).1 key).data) :
    ∃ site ∈ calls native1 native2 copy allocator id H store schedule,
      Birth native1 copy allocator id key
        ((run native1 native2 copy allocator id H store schedule).1 key).data site := by
  rcases Hir_ScheduleOrigin.origin_or_initial native1 native2 copy allocator id H store schedule key allowed owner marker with old | fresh
  · rw [old] at owner marker
    exact False.elim (genesis key owner marker)
  · exact fresh

#print axioms selected_writer
end AspisR1.Hir_GenesisOrigin
end
