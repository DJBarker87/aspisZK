import R1Z.PV_DL_ArrayTransfer
import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_ArrayNative
set_option autoImplicit false

/-- Owned sequential reference for the safe Rust from_fn(next) reference.
Both the length rejection and potential short-iterator panic are explicit. -/
def reference {T : Type} (N : Usize) (v : alloc.vec.Vec T) :
    Result (core.result.Result (Array T N) (alloc.vec.Vec T)) := do
  if v.val.length=N.val then
    let (owned,remaining) ← PV_DL_ArrayTransfer.drain N.val v.val
    if h : owned.length=N.val then ok (.Ok ⟨owned,h⟩) else fail .panic
  else ok (.Err v)

/-- Complete Result equality with the native bulk-transfer ownership model;
no operation, bounds, success, Copy, Clone or destructor premise is supplied. -/
theorem source_reference {T : Type} (N : Usize) (v : alloc.vec.Vec T) :
    reference N v=ok (PV_DL_ArrayOwnership.value N v) := by
  by_cases h : v.val.length=N.val
  · simp only [reference,if_pos h]
    rw [← h,PV_DL_ArrayTransfer.exact_transfer]
    simp only [bind_tc_ok,PV_DL_ArrayOwnership.value,dif_pos h]
  · simp only [reference,if_neg h,PV_DL_ArrayOwnership.value,dif_neg h]

@[reducible] def selected [types : ExternalTypes] (ops : ExternalFuns) : ExternalFuns :=
  {ops with op36 := fun _ N v => ok (PV_DL_ArrayOwnership.value N v)}

theorem selected_native [types : ExternalTypes] (ops : ExternalFuns) {T : Type}
    (A : Type) (N : Usize) (v : alloc.vec.Vec T) :
    @Array.Insts.CoreConvertTryFromVecVec.try_from types (selected ops) T A N v=
      reference N v := by
  exact (source_reference N v).symm

theorem nonvacuous :
    ∃ v : alloc.vec.Vec Unit, ∃ a : Array Unit 0#usize,
      reference 0#usize v=ok (.Ok a) := by
  let v : alloc.vec.Vec Unit := ⟨[],by simp⟩
  exact ⟨v,⟨[],rfl⟩,by rw [source_reference];rfl⟩

#print axioms reference
#print axioms source_reference
#print axioms selected
#print axioms selected_native
#print axioms nonvacuous
end R1Z.PV_DL_ArrayNative
