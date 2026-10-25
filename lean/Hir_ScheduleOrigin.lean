import Hir_CallBirth
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_ScheduleOrigin
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Every selected initialized verifier account either predates this schedule
unchanged, or has an ACTUAL successful native writer in its reached calls.
The predecessor alternative is explicit; arbitrary initial ledger contents do
not become source-proved provenance. -/
theorem origin_or_initial {A B : Type}
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (store : Store) (schedule : Schedule A B) (key : Nat)
    (allowed : admissible native1 native2 copy allocator id H store schedule)
    (owner : ((run native1 native2 copy allocator id H store schedule).1 key).owner = id)
    (marker : Initialized ((run native1 native2 copy allocator id H store schedule).1 key).data) :
    (run native1 native2 copy allocator id H store schedule).1 key = store key ∨
      ∃ site ∈ calls native1 native2 copy allocator id H store schedule,
        Birth native1 copy allocator id key
          ((run native1 native2 copy allocator id H store schedule).1 key).data site := by
  induction schedule generalizing store with
  | done value => exact Or.inl rfl
  | inspect k ih => exact ih store store allowed owner marker
  | ask query k ih => exact ih (H query) store allowed owner marker
  | rollback k ih => exact ih store allowed owner marker
  | invoke call k ih =>
    let head := Hir_Call.native native1 native2 copy allocator id store call
    rcases ih head.2.2 head.1 allowed owner marker with old | ⟨site,member,birth⟩
    · rcases Hir_CallBirth.unchanged_or_birth native1 native2 copy allocator id store call key with same | fresh
      · exact Or.inl (old.trans same)
      · right
        refine ⟨⟨store,call⟩,List.mem_cons_self,?_⟩
        change Birth native1 copy allocator id key
          ((run native1 native2 copy allocator id H head.1 (k head.2.2)).1 key).data ⟨store,call⟩
        rw [old]
        exact fresh
    · exact Or.inr ⟨site,List.mem_cons_of_mem _ member,birth⟩
  | foreign caller address value k ih =>
    let head := Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller address value)
    rcases ih head.2 head.1 allowed.2 owner marker with old | fresh
    · left
      have unchanged := Hir_ForeignBack.unchanged native1 copy allocator id store caller address key value allowed.1
        (by rw [← old]; exact owner) (by rw [← old]; exact marker)
      exact old.trans unchanged
    · exact Or.inr fresh

#print axioms origin_or_initial
end AspisR1.Hir_ScheduleOrigin
end
