import NDO_JGj_LocalPackedTotal
import RPv_FJb_TailRow
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ExternalTailRowTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
theorem source (q : NQ) (sums : FJb_ColumnTable.Table) (index : Usize)
    (hs : FJb_TailCell.Bounded sums) :
    ∃ out,FJb_TailRow.step q sums index=ok out ∧ Canon out := by
  obtain ⟨raw,rr⟩ := FJb_BuilderTotal.value 4#usize core.marker.CopyU64
    FJb_TailRow.callback 0#u64 (FJb_LimbMap.words q,sums,index) (by
      intro i hi
      obtain ⟨x,hx,_,_⟩ := FJb_TailCell.value (FJb_LimbMap.words q) sums index i hi hs
      exact ⟨x,hx⟩)
  obtain ⟨out,ro,co⟩ := JGj_LocalPackedTotal.converted raw
  refine ⟨out,?_,co⟩
  unfold FJb_TailRow.step
  change (do
    let raw ← array_from_fn_copy 4#usize core.marker.CopyU64 FJb_TailRow.callback
      0#u64 (FJb_LimbMap.words q,sums,index)
    state_only_poseidon.extension_from_raw_limbs raw)=ok out
  rw [rr,bind_tc_ok,ro]
#print axioms source
end AspisR1.JGj_ExternalTailRowTotal
end
