import RPz8_CPH_FixtureShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_FixtureReserve
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPH_FixtureData

theorem reserve_ok (sizes : List Nat) : reserve allocator sizes () = ok () := by
  induction sizes with
  | nil => rfl
  | cons n ns ih => simpa only [reserve,allocator,S2W_Trace.thenResult] using ih

theorem copy_lengths :
    ((S2Trust.acquire e1.heap (e1.heap.accounts 2).1 0 0 .exclusive).payload
      (e1.heap.accounts 2).1).descriptor.length =
      (S2W_CommittedCheckpoint.source (S2W_ReturnedCheckpoint.nativeBytes saved)).descriptor.length := by
  have unchanged : (S2Trust.acquire e1.heap (e1.heap.accounts 2).1 0 0 .exclusive).payload = e1.heap.payload := rfl
  rw [unchanged]
  change (e1.buffers 2).val.length = (S2W_ReturnedCheckpoint.nativeBytes saved).length
  rw [S2W_ReturnedCheckpoint.nativeBytes,List.length_map,
    CPH_FixtureShape.size_before,CPH_FixtureShape.size_saved]

#print axioms reserve_ok
#print axioms copy_lengths
end AspisR1.CPH_FixtureReserve
end
