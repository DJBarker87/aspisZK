import RPx_Deployed
import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCL_WrapperLength
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws

/-- Acceptance of the actual copy in the wrapper determines saved length.
No independently supplied savedSize or selected child return is assumed. -/
theorem source {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (destination : (e.heap.payload (e.heap.accounts 2).1).descriptor.length = 1768)
    (accepted : first native copy allocator e program data state = ok (.Ok (saved,post,final))) :
    saved.val.length = 1768 := by
  unfold first at accepted
  obtain ⟨allocated,_,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ accepted
  obtain ⟨result,_,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  cases result with
  | Err error => cases rest
  | Ok value =>
    dsimp only at rest
    cases copied : copy (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive)
        (e.heap.accounts 2).1 (S2W_CommittedCheckpoint.source (nativeBytes value)) with
    | panic => simp only [copied] at rest; cases rest
    | returned written =>
      rw [copied] at rest
      obtain ⟨cleaned,_,returned⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
      have equal := core.result.Result.Ok.inj (Result.ok.inj returned)
      have same : value = saved := congrArg Prod.fst equal
      subst value
      have spec := std.slice_copy_from_slice
        (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive) (e.heap.accounts 2).1
        (S2W_CommittedCheckpoint.source (nativeBytes saved))
      rw [copied] at spec
      unfold specification at spec
      split at spec
      · rename_i lengths
        simpa only [acquire,S2W_CommittedCheckpoint.source,nativeBytes,List.length_map,destination]
          using lengths.symm
      · cases spec
#print axioms source
end AspisR1.NCL_WrapperLength
end
