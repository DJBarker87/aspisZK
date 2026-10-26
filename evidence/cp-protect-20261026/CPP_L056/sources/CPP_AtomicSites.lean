import CPP_AtomicSchedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicSites
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem member {A B : Type} (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (before : Store) (code : CPP_Schedule.Schedule A (CPP_Atomic.Reply B)) (site : CallAt A)
    (member : site ∈ CPP_Atomic.sites n1 n2 copy allocator id H before code) :
    CPP_Atomic.committed (CPP_Schedule.run n1 n2 copy allocator id H before code).2.2 ∧
      site ∈ calls n1 n2 copy allocator id H before (CPP_Schedule.erase code) := by
  cases reply : (CPP_Schedule.run n1 n2 copy allocator id H before code).2.2 with
  | fail error => simp only [CPP_Atomic.sites,reply] at member; cases member
  | div => simp only [CPP_Atomic.sites,reply] at member; cases member
  | ok result => cases result with
    | Err error => simp only [CPP_Atomic.sites,reply] at member; cases member
    | Ok value =>
      simp only [CPP_Atomic.sites,reply] at member
      exact ⟨⟨value,rfl⟩,member⟩

#print axioms member
end AspisR1.CPP_AtomicSites
end
