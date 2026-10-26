import CPP_AtomicSchedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicRunOrigin
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_ProvenanceModel CPP_AtomicSchedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem origin_or_initial {A B : Type}
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (before : Store) (schedule : Schedule A B) (key : Nat)
    (allowed : CPP_AtomicSchedule.admissible n1 n2 copy allocator id H before schedule)
    (owner : ((run n1 n2 copy allocator id H before schedule).1 key).owner = id)
    (marker : Initialized ((run n1 n2 copy allocator id H before schedule).1 key).data) :
    (run n1 n2 copy allocator id H before schedule).1 key = before key ∨
      ∃ site ∈ sites n1 n2 copy allocator id H before schedule,
        Birth n1 copy allocator id key ((run n1 n2 copy allocator id H before schedule).1 key).data site := by
  induction schedule generalizing before with
  | done value => exact Or.inl rfl
  | inspect k ih => exact ih before before allowed owner marker
  | ask query k ih => exact ih (H query) before allowed owner marker
  | transaction code k ih =>
    let head := CPP_Atomic.run n1 n2 copy allocator id H before code
    rcases ih head.2.2 head.1 allowed.2 owner marker with old | ⟨site,member,birth⟩
    · have headOwner : (head.1 key).owner = id := by rw [← old]; exact owner
      have headMarker : Initialized (head.1 key).data := by rw [← old]; exact marker
      rcases CPP_AtomicOrigin.origin_or_initial n1 n2 copy allocator id H before code key allowed.1 headOwner headMarker with same | ⟨site,member,birth⟩
      · exact Or.inl (old.trans same)
      · right
        refine ⟨site,List.mem_append_left _ member,?_⟩
        change Birth n1 copy allocator id key
          ((run n1 n2 copy allocator id H head.1 (k head.2.2)).1 key).data site
        rw [old]
        exact birth
    · exact Or.inr ⟨site,List.mem_append_right _ member,birth⟩

#print axioms origin_or_initial
end AspisR1.CPP_AtomicRunOrigin
end
