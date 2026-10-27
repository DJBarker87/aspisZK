import RPv_FJb_RawRowCallbacks
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedRawCallbacks
open Aeneas Aeneas.Std Result FIq_Native
open FJb_RawRowCallbacks (Input)
abbrev call := state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
/-- The native packed helper uses the already-checked raw matrix callback,
with identical input/row/limb carriers and operation order. -/
theorem same (input : Input) (row limb : Usize) :
    call (input,row) limb=FJb_RawRowCallbacks.call (input,row) limb := rfl

theorem total (input : Input) (row limb : Usize) (hr : row.val<4) (hl : limb.val<4) :
    ∃ x,call (input,row) limb=ok (x,(input,row)) := by
  obtain ⟨x,hx⟩ := FJb_RawRowCallbacks.total input row limb hr hl
  exact ⟨x,(same input row limb).trans hx⟩
#print axioms same
#print axioms total
end AspisR1.FJe_PackedRawCallbacks
end
