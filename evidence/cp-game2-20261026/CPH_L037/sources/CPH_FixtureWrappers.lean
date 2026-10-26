import CPH_FixtureReserve
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_FixtureWrappers
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPH_FixtureData CPH_FixtureReserve S2W_CommittedCheckpoint S2W_ReturnedCheckpoint
open S2W_WrapperLaws S2W_TrustedStd

def post1 := writeBracket e1.heap 2 0 0 (source (nativeBytes saved))

/-- Both native wrappers actually evaluate in the same nonaliased game model.
The n1/n2 functions are local witnesses; DrvC extraction is deliberately not asserted. -/
theorem first_success (data : Slice U8) :
    first n1 copy allocator e1 id data () = ok (.Ok (saved,post1,())) := by
  simp only [first,reserve_ok,n1]
  change (match copy (acquire e1.heap (e1.heap.accounts 2).1 0 0 .exclusive)
      (e1.heap.accounts 2).1 (source (nativeBytes saved)) with
    | .panic => .fail .assertionFailure
    | .returned written => ok (.Ok (saved,release written (exclusiveGuard e1.heap 2 0 0),())) :
      Result (core.result.Result (alloc.vec.Vec U8 × Heap (Nat → Record) × Unit) AdapterRw.Cuts.PE)) =
        ok (.Ok (saved,post1,()))
  rw [show copy (acquire e1.heap (e1.heap.accounts 2).1 0 0 .exclusive)
      (e1.heap.accounts 2).1 (source (nativeBytes saved)) =
      .returned (copyHeap (acquire e1.heap (e1.heap.accounts 2).1 0 0 .exclusive)
        (e1.heap.accounts 2).1 (source (nativeBytes saved))) from if_pos copy_lengths]
  rfl

theorem second_success (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    second n2 allocator e2 id data slot () = ok (.Ok (e2.heap,())) := by
  simp only [second,reserve_ok,n2]
  rfl

#print axioms first_success
#print axioms second_success
end AspisR1.CPH_FixtureWrappers
end
