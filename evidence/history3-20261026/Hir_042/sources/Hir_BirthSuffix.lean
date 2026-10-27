import Hir_CallSuccess
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_BirthSuffix
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- The suffix is from the ACTUAL measured schedule, not an invented empty
history or a separately chosen list. Source zero/owner checks classify it. -/
theorem suffix {A B : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data,
      AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = native1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (trustedCopy : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (H : Bytes → State) (store : Store) (schedule : Schedule A B)
    (site : CallAt A) (key : Nat) (data : Slice U8)
    (member : site ∈ calls native1 native2 copy allocator id H store schedule)
    (birth : Birth native1 copy allocator id key data site) :
    ∃ (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
      (front events : List S2X.AccountEvent),
      first native1 copy allocator (load site.before site.call.layout) id site.call.data site.call.state =
        ok (.Ok (saved,post,final)) ∧ data = saved.deref ∧
      Trace ops id (commit site.before key saved) events
        (run native1 native2 copy allocator id H store schedule).1 ∧
      (run native1 native2 copy allocator id H store schedule).2.1 =
        front ++ (.committedWrite key (MultiproofConeCanonical.bytesOf saved.val) :: events) := by
  induction schedule generalizing store with
  | done value => cases member
  | inspect k ih => exact ih store store member
  | ask query k ih => exact ih (H query) store member
  | invoke call k ih =>
    let head := Hir_Call.native native1 native2 copy allocator id store call
    rcases List.mem_cons.mp member with same | tail
    · subst site
      obtain ⟨route,keyEq,saved,post,final,accepted,dataEq⟩ := birth
      change (call.layout.handles 2).1 = key at keyEq
      subst key
      have effect := Hir_CallSuccess.effect native1 native2 copy allocator id store call saved post final route accepted
      refine ⟨saved,post,final,[],(run native1 native2 copy allocator id H head.1 (k head.2.2)).2.1,
        accepted,dataEq,?_,?_⟩
      · have trace := Hir_ScheduleTrace.classified ops law native1 native2 source copy trustedCopy allocator id H
          head.1 (k head.2.2)
        simpa only [head,effect,Hir_Schedule.run] using trace
      · simp only [Hir_Schedule.run,head,effect,List.nil_append]
    · obtain ⟨saved,post,final,front,events,accepted,dataEq,trace,history⟩ := ih head.2.2 head.1 tail
      refine ⟨saved,post,final,head.2.1 :: front,events,accepted,dataEq,trace,?_⟩
      change head.2.1 :: (run native1 native2 copy allocator id H head.1 (k head.2.2)).2.1 = _
      rw [history]
      rfl
  | foreign caller address value k ih =>
    let head := Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller address value)
    obtain ⟨saved,post,final,front,events,accepted,dataEq,trace,history⟩ := ih head.2 head.1 member
    refine ⟨saved,post,final,head.2 :: front,events,accepted,dataEq,trace,?_⟩
    change head.2 :: (run native1 native2 copy allocator id H head.1 (k head.2)).2.1 = _
    rw [history]
    rfl
  | rollback k ih =>
    obtain ⟨saved,post,final,front,events,accepted,dataEq,trace,history⟩ := ih store member
    refine ⟨saved,post,final,.rollback :: front,events,accepted,dataEq,trace,?_⟩
    change .rollback :: (run native1 native2 copy allocator id H store k).2.1 = _
    rw [history]
    rfl

#print axioms suffix
end AspisR1.Hir_BirthSuffix
end
