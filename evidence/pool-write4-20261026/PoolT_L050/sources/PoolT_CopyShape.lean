import PoolT_Verifier
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolT_CopyShape
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open MultiproofConeCanonical

/-- Wrapper acceptance itself forces equal copy lengths, even for an arbitrary
owned child. No extraction, child-success observation or buffer-size assumption. -/
theorem accepted_lengths {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first native copy allocator e program data state = ok (.Ok (saved,post,final))) :
    (e.heap.payload (e.heap.accounts 2).1).descriptor.length = saved.val.length := by
  unfold first at accepted
  obtain ⟨allocated,_,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ accepted
  obtain ⟨result,_,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  cases result with
  | Err error => cases rest
  | Ok value =>
    dsimp only at rest
    cases copied : copy (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive)
        (e.heap.accounts 2).1 (source (nativeBytes value)) with
    | panic => simp only [copied] at rest; cases rest
    | returned written =>
      rw [copied] at rest
      obtain ⟨cleaned,_,returned⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
      have equal := core.result.Result.Ok.inj (Result.ok.inj returned)
      have same : value = saved := congrArg Prod.fst equal
      subst value
      have lengths : ((acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive).payload
          (e.heap.accounts 2).1).descriptor.length = (source (nativeBytes saved)).descriptor.length := by
        by_contra different
        have panic := mismatched_copy copy std _ _ _ different
        rw [copied] at panic
        cases panic
      simpa only [acquire,source,nativeBytes,List.length_map] using lengths

/-- Complete returned bytes at the actual post-copy cell, at the size forced by
this invocation. This has no source/refinement or1768-size premise. -/
theorem accepted_bytes {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first native copy allocator e program data state = ok (.Ok (saved,post,final))) :
    payloadBytes encode (post.payload (e.heap.accounts 2).1) saved.val.length = bytesOf saved.val := by
  have lengths := accepted_lengths native copy std allocator e program data state final saved post accepted
  have written := (first_accepted native copy std allocator e program data state final saved post accepted).2
  rw [written,write_bracket e.heap 2 0 0 (source (nativeBytes saved)) rfl rfl]
  have content : payloadBytes encode ((copyHeap e.heap (e.heap.accounts 2).1
      (source (nativeBytes saved))).payload (e.heap.accounts 2).1) saved.val.length =
      payloadBytes encode (source (nativeBytes saved)) saved.val.length := by
    apply congrArg List.ofFn
    funext i
    change encode (if i.val < (e.heap.payload (e.heap.accounts 2).1).descriptor.length
      then (source (nativeBytes saved)).contents i.val
      else (e.heap.payload (e.heap.accounts 2).1).contents i.val) = _
    rw [if_pos (lengths.symm ▸ i.isLt)]
  rw [content]
  have size : (nativeBytes saved).length = saved.val.length := by simp only [nativeBytes,List.length_map]
  rw [← size,source_bytes,vector_representation]

#print axioms accepted_lengths
#print axioms accepted_bytes
end AspisR1.PoolT_CopyShape
end
