import NDO_JGj_LocalPackedTotal
import RPv_FJb_RawRowCallbacks
import RPv_FJb_BuilderTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ExternalRowTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
theorem source (input : FJb_RawRowCallbacks.Input) (r : Usize) (hr : r.val<4) :
    ∃ out,state_only_poseidon.external_linear_lazy_row input r=ok out ∧ Canon out := by
  obtain ⟨raw,rr⟩ := FJb_BuilderTotal.value 4#usize core.marker.CopyU64
    state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
    0#u64 (input,r) (by intro i hi;exact FJb_RawRowCallbacks.total input r i hr hi)
  obtain ⟨out,ro,co⟩ := JGj_LocalPackedTotal.converted raw
  refine ⟨out,?_,co⟩
  unfold state_only_poseidon.external_linear_lazy_row
  rw [rr,bind_tc_ok,ro]
#print axioms source
end AspisR1.JGj_ExternalRowTotal
end
