import NDO_JGj_InternalLaneCall
import NDO_JGj_ExtensionWords
import RPv_JFy_ArrayTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalLaneStep
open Aeneas Aeneas.Std Result FIq_Native
open JGj_RawBounds
open FJb_MatrixGroupStep (State)
def step (s : State) (full : Raw) (lane : Usize) : Result State := do
  let x ← Array.index_usize s lane
  let limbs ← state_only_poseidon.extension_limbs x
  let raw ← array_from_fn_copy 4#usize core.marker.CopyU64 JGj_InternalLaneCall.Callback 0#u64 (full,limbs,lane)
  let q ← state_only_poseidon.extension_from_raw_limbs raw
  Array.update s lane q
theorem source (s : State) (full : Raw) (lane : Usize)
    (hl : 1≤lane.val) (hh : lane.val<16) (hs : FIw_ArrayValue.canonical s) (hf : Bound full (62*P)) :
    ∃ out,step s full lane=ok out ∧ FIw_ArrayValue.canonical out := by
  obtain ⟨x,rx,cx⟩ := JFy_ArrayTotal.read s lane hh hs
  have cw := JGj_ExtensionWords.canonical x cx
  obtain ⟨raw,rr⟩ := FJb_BuilderTotal.value 4#usize core.marker.CopyU64 JGj_InternalLaneCall.Callback
    0#u64 (full,FJb_LimbMap.words x,lane) (by intro i hi;exact JGj_InternalLaneCall.source full _ lane i hl hh hi hf cw)
  obtain ⟨q,rq,cq⟩ := JGj_LocalPackedTotal.converted raw
  obtain ⟨out,ro,co⟩ := JFy_ArrayTotal.update s lane q hh hs cq
  refine ⟨out,?_,co⟩
  unfold step
  rw [rx,bind_tc_ok]
  change (do let raw ← array_from_fn_copy 4#usize core.marker.CopyU64 JGj_InternalLaneCall.Callback 0#u64 (full,FJb_LimbMap.words x,lane)
             let q ← state_only_poseidon.extension_from_raw_limbs raw
             Array.update s lane q)=ok out
  rw [rr,bind_tc_ok,rq,bind_tc_ok,ro]
theorem unfold_loop (iter : core.ops.range.Range Usize) (s : State) (full : Raw) :
    state_only_poseidon.internal_linear_lazy_loop1 iter s full=(do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok s
      | some lane => do
        let next ← step s full lane
        state_only_poseidon.internal_linear_lazy_loop1 iter1 next full) := by
  rw [state_only_poseidon.internal_linear_lazy_loop1.eq_def]
  simp only [step,bind_assoc_eq]
  rfl
#print axioms source
#print axioms unfold_loop
end AspisR1.JGj_InternalLaneStep
end
