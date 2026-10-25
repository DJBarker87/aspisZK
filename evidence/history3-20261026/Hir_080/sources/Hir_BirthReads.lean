import Hir_CommonEvent
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_BirthReads
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem source_reads {A B F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (initial : Store) (schedule : Schedule A B) (site : CallAt A)
    (member : site ∈ calls native1 native2 copy allocator id H initial schedule) :
    ∃ front back,
      Hir_ScheduleLog.reads c hashv native1 native2 copy allocator id H initial schedule =
        front ++ SdkC_Source.readLog (Hir_CallLog.attempts c hashv copy allocator id site.before site.call) ++ back := by
  induction schedule generalizing initial with
  | done value => cases member
  | inspect k ih => exact ih initial initial member
  | ask query k ih =>
    obtain ⟨front,back,eq⟩ := ih (H query) initial member
    exact ⟨(query,H query) :: front,back,by simp only [Hir_ScheduleLog.reads,eq,List.cons_append]⟩
  | invoke call k ih =>
    let head := Hir_Call.native native1 native2 copy allocator id initial call
    rcases List.mem_cons.mp member with same | tail
    · subst site
      exact ⟨[],Hir_ScheduleLog.reads c hashv native1 native2 copy allocator id H head.1 (k head.2.2),rfl⟩
    · obtain ⟨front,back,eq⟩ := ih head.2.2 head.1 tail
      refine ⟨SdkC_Source.readLog (Hir_CallLog.attempts c hashv copy allocator id initial call) ++ front,back,?_⟩
      dsimp only [head] at eq
      simp only [Hir_ScheduleLog.reads,eq,List.append_assoc]
  | foreign caller key value k ih =>
    let head := Hiq_NativeAction.apply native1 copy allocator id initial (.foreign caller key value)
    exact ih head.2 head.1 member
  | rollback k ih => exact ih initial member

#print axioms source_reads
end AspisR1.Hir_BirthReads
end
