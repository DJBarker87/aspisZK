import NGK_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGR_HISTORY
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_ReturnedCheckpoint S2W_CommittedCheckpoint
open S2W_WrapperLaws S2W_EntryWriteHistory MultiproofConeCanonical

/-- Acceptance of the actual interpreted copy supplies its length domain.
No destination-size premise or source-extraction equality is added. -/
theorem native_copy_length {A : Type} (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first n1 copy allocator e id data state = ok (.Ok (saved,post,final))) :
    (e.heap.payload (e.heap.accounts 2).1).descriptor.length = saved.val.length := by
  unfold first at accepted
  obtain ⟨allocated, _, rest⟩ := AdapterRw.Cuts.bind_success _ _ _ accepted
  obtain ⟨result, _, rest⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  cases result with
  | Err error => cases rest
  | Ok value =>
    dsimp only at rest
    cases copied : copy (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive)
        (e.heap.accounts 2).1 (source (nativeBytes value)) with
    | panic => simp only [copied] at rest; cases rest
    | returned written =>
      rw [copied] at rest
      obtain ⟨cleaned, _, returned⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
      have same : value = saved := congrArg Prod.fst (core.result.Result.Ok.inj (Result.ok.inj returned))
      subst value
      have actual := std.slice_copy_from_slice
        (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive) (e.heap.accounts 2).1
        (source (nativeBytes saved))
      rw [copied] at actual
      unfold specification at actual
      split at actual
      · rename_i lengths
        simpa only [acquire, source, nativeBytes, List.length_map] using lengths
      · cases actual

/-- The account2 post-write payload is the returned checkpoint. Only accepted
std semantics are consumed; no independently supplied write equality. -/
theorem native_written_bytes {A : Type} (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first n1 copy allocator e id data state = ok (.Ok (saved,post,final)))
    (savedSize : saved.val.length = 1768) :
    payloadBytes encode (post.payload (e.heap.accounts 2).1) 1768 = bytesOf saved.val := by
  have written := (first_accepted n1 copy std allocator e id data state final saved post accepted).2
  have size := (native_copy_length n1 copy std allocator e id data state final saved post accepted).trans savedSize
  rw [written, written_bytes encode e.heap 2 0 0 (source (nativeBytes saved)) rfl rfl size]
  have nativeSize : (nativeBytes saved).length = 1768 := by
    simpa only [nativeBytes, List.length_map] using savedSize
  rw [← nativeSize, source_bytes, vector_representation]

#print axioms native_copy_length
#print axioms native_written_bytes
end AspisR1.NGR_HISTORY
end
