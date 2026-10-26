import CPP_AtomicSource
import Hir_ScheduleOrigin
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicOrigin
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_ProvenanceModel
open CPP_Atomic
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
attribute [local instance] Classical.propDecidable

theorem origin_or_initial {A B : Type}
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (before : Store) (code : CPP_Schedule.Schedule A (CPP_Atomic.Reply B)) (key : Nat)
    (allowed : committed (CPP_Schedule.run n1 n2 copy allocator id H before code).2.2 →
      admissible n1 n2 copy allocator id H before (CPP_Schedule.erase code))
    (owner : ((CPP_Atomic.run n1 n2 copy allocator id H before code).1 key).owner = id)
    (marker : Initialized ((CPP_Atomic.run n1 n2 copy allocator id H before code).1 key).data) :
    (CPP_Atomic.run n1 n2 copy allocator id H before code).1 key = before key ∨
      ∃ site ∈ CPP_Atomic.sites n1 n2 copy allocator id H before code,
        Birth n1 copy allocator id key ((CPP_Atomic.run n1 n2 copy allocator id H before code).1 key).data site := by
  by_cases success : committed (CPP_Schedule.run n1 n2 copy allocator id H before code).2.2
  · obtain ⟨value,reply⟩ := success
    rw [CPP_Atomic.run,CPP_AtomicLaws.commit before _ ⟨value,reply⟩] at owner marker ⊢
    rw [CPP_RunErasure.exact] at owner marker ⊢
    have rawReply := reply
    rw [CPP_RunErasure.exact] at rawReply
    simp only [CPP_Atomic.sites,CPP_RunErasure.exact,rawReply]
    exact Hir_ScheduleOrigin.origin_or_initial n1 n2 copy allocator id H before (CPP_Schedule.erase code) key
      (allowed ⟨value,reply⟩) owner marker
  · left
    rw [CPP_Atomic.run,CPP_AtomicLaws.rollback before _ success]

#print axioms origin_or_initial
end AspisR1.CPP_AtomicOrigin
end
