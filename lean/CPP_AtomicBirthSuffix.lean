import CPP_AtomicSites
import Hir_BirthSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicBirthSuffix
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem suffix {A B : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (H : Bytes → State) (before : Store)
    (code : CPP_Schedule.Schedule A (CPP_Atomic.Reply B)) (site : CallAt A) (key : Nat) (data : Slice U8)
    (member : site ∈ CPP_Atomic.sites n1 n2 copy allocator id H before code)
    (birth : Birth n1 copy allocator id key data site) :
    ∃ saved post final front events,
      first n1 copy allocator (load site.before site.call.layout) id site.call.data site.call.state = ok (.Ok (saved,post,final)) ∧
      data = saved.deref ∧
      Trace ops id (commit site.before key saved) events (CPP_Atomic.run n1 n2 copy allocator id H before code).1 ∧
      (CPP_Atomic.run n1 n2 copy allocator id H before code).2.1 =
        front ++ (.committedWrite key (MultiproofConeCanonical.bytesOf saved.val) :: events) := by
  obtain ⟨success,rawMember⟩ := CPP_AtomicSites.member n1 n2 copy allocator id H before code site member
  rw [CPP_Atomic.run,CPP_AtomicLaws.commit before _ success,CPP_RunErasure.exact]
  exact Hir_BirthSuffix.suffix ops law n1 n2 source copy std allocator id H before
    (CPP_Schedule.erase code) site key data rawMember birth

#print axioms suffix
end AspisR1.CPP_AtomicBirthSuffix
end
