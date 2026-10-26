import ARQ_FirstBody
import F3X_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_AccountPrefix
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment SCE_Execution

/-- A TX1 read remains in the complete response-driven account, regardless
of the second choice's fresh reads and regardless of TX2 acceptance. -/
theorem first_read {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      ok (.Ok (saved,post,final))) (addr : Bytes)
    (read : FS2.Duplex.Read (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).1 addr) :
    FS2.Duplex.Read (eval H (account c hashv copy allocator id a)).1 addr := by
  rw [accepted_eval c hashv copy allocator id a H saved post final first]
  change addr ∈ ((eval H a.first).1 ++
    ((eval H (firstCode c hashv copy allocator id (eval H a.first).2)).1 ++ _)).map Prod.fst
  rw [List.map_append,List.map_append]
  exact List.mem_append_right _ (List.mem_append_left _ read)

/-- Exact first wrapper log, as constructed from its own ideal trace, is
retained as one chronological interior block, not erased or reordered. -/
theorem first_log_block {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      ok (.Ok (saved,post,final))) :
    ∃ log tail,
      S2W_Trace.run (SCH_IdealSdk.dictionary c hashv H)
        (S2W_Outer.stage1_owned (SCH_IdealSdk.dictionary c hashv H)
          S2W_Outer.traceEffects id (eval H a.first).2.entry.first (eval H a.first).2.data)
        [] = ok (.Ok saved,log) ∧
      (eval H (account c hashv copy allocator id a)).1 =
        (eval H a.first).1 ++ (ARQ_LowerTrace.trace c hashv H log ++ tail) := by
  obtain ⟨log,ran,same⟩ := ARQ_FirstBody.accepted c hashv copy allocator id _ saved post final H first
  refine ⟨log,_,ran,?_⟩
  rw [accepted_eval c hashv copy allocator id a H saved post final first,same]

#print axioms first_read
#print axioms first_log_block
end AspisR1.ARQ_AccountPrefix
end
