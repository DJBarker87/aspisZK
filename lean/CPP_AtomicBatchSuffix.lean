import CPP_AtomicBirthSuffix
import CPP_AtomicRunTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicBatchSuffix
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_ProvenanceModel CPP_AtomicSchedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem suffix {A B : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (H : Bytes → State) (before : Store)
    (schedule : Schedule A B) (site : CallAt A) (key : Nat) (data : Slice U8)
    (member : site ∈ sites n1 n2 copy allocator id H before schedule)
    (birth : Birth n1 copy allocator id key data site) :
    ∃ saved post final front events,
      first n1 copy allocator (load site.before site.call.layout) id site.call.data site.call.state = ok (.Ok (saved,post,final)) ∧
      data = saved.deref ∧
      Trace ops id (commit site.before key saved) events (run n1 n2 copy allocator id H before schedule).1 ∧
      (run n1 n2 copy allocator id H before schedule).2.1 =
        front ++ (.committedWrite key (MultiproofConeCanonical.bytesOf saved.val) :: events) := by
  induction schedule generalizing before with
  | done value => cases member
  | inspect k ih => exact ih before before member
  | ask query k ih => exact ih (H query) before member
  | transaction code k ih =>
    let head := CPP_Atomic.run n1 n2 copy allocator id H before code
    let tail := run n1 n2 copy allocator id H head.1 (k head.2.2)
    rcases List.mem_append.mp member with here | later
    · obtain ⟨saved,post,final,front,events,accepted,dataEq,trace,history⟩ :=
        CPP_AtomicBirthSuffix.suffix ops law n1 n2 source copy std allocator id H before code site key data here birth
      refine ⟨saved,post,final,front,events ++ tail.2.1,accepted,dataEq,?_,?_⟩
      · exact CPP_TraceAppend.append ops id trace
          (CPP_AtomicRunTrace.classified ops law n1 n2 source copy std allocator id H head.1 (k head.2.2))
      · change head.2.1 ++ tail.2.1 = _
        change head.2.1 = _ at history
        rw [history]
        simp only [List.append_assoc,List.cons_append]
    · obtain ⟨saved,post,final,front,events,accepted,dataEq,trace,history⟩ := ih head.2.2 head.1 later
      refine ⟨saved,post,final,head.2.1 ++ front,events,accepted,dataEq,trace,?_⟩
      change head.2.1 ++ tail.2.1 = _
      change tail.2.1 = _ at history
      rw [history,List.append_assoc]

#print axioms suffix
end AspisR1.CPP_AtomicBatchSuffix
end
