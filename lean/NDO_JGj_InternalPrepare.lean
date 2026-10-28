import NDO_JGj_InternalAccState
import NDO_JGj_InternalFullSum
import NDO_JGj_InternalZeroStable
import NDO_JGj_BoundedRawBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalPrepare
open Aeneas Aeneas.Std Result FIq_Native
open JGj_RawBounds
open FJb_MatrixGroupStep (State)
def source (s : State) : Result (State × Raw) := do
  let x ← Array.index_usize s 0#usize
  let old ← state_only_poseidon.extension_limbs x
  let part ← state_only_poseidon.internal_linear_lazy_loop0 s (Array.repeat 4#usize 0#u64) 1#usize
  let full ← array_from_fn_copy 4#usize core.marker.CopyU64 JGj_InternalFullSum.Full 0#u64 (part,old)
  let zero ← array_from_fn_copy 4#usize core.marker.CopyU64 JGj_InternalZeroEquation.Callback 0#u64 (part,old)
  let q ← state_only_poseidon.extension_from_raw_limbs zero
  let s1 ← Array.update s 0#usize q
  ok (s1,full)
theorem success (s : State) (hs : FIw_ArrayValue.canonical s) :
    ∃ s1 full,source s=ok (s1,full) ∧ FIw_ArrayValue.canonical s1 ∧ Bound full (62*P) := by
  obtain ⟨x,rx,cx⟩ := JFy_ArrayTotal.read s 0#usize (by decide) hs
  have cw := JGj_ExtensionWords.canonical x cx
  have initial : Bound (Array.repeat 4#usize 0#u64) (1*P) := by
    intro j
    simp only [FJb_TailCell.cell,Array.repeat,List.getElem_replicate]
    norm_num [P,AspisV8R17.RawReducer.P]
  obtain ⟨part,rp,bp⟩ := JGj_InternalAccState.source 15 1#usize s _ 1 rfl (by decide) hs initial
  have bp61 : Bound part (61*P) := bp
  obtain ⟨full,rf,bf⟩ := JGj_BoundedRawBuilder.source JGj_InternalFullSum.Full (part,FJb_LimbMap.words x) (62*P)
    (by intro i hi;exact JGj_InternalFullSum.full part _ i hi bp61 cw)
  obtain ⟨zero,rz⟩ := FJb_BuilderTotal.value 4#usize core.marker.CopyU64 JGj_InternalZeroEquation.Callback
    0#u64 (part,FJb_LimbMap.words x) (by intro i hi;exact JGj_InternalZeroStable.source part _ i hi bp61 cw)
  obtain ⟨q,rq,cq⟩ := JGj_LocalPackedTotal.converted zero
  obtain ⟨s1,rs,cs⟩ := JFy_ArrayTotal.update s 0#usize q (by decide) hs cq
  refine ⟨s1,full,?_,cs,bf⟩
  unfold source
  rw [rx,bind_tc_ok]
  change (do
    let part ← state_only_poseidon.internal_linear_lazy_loop0 s (Array.repeat 4#usize 0#u64) 1#usize
    let full ← array_from_fn_copy 4#usize core.marker.CopyU64 JGj_InternalFullSum.Full 0#u64 (part,FJb_LimbMap.words x)
    let zero ← array_from_fn_copy 4#usize core.marker.CopyU64 JGj_InternalZeroEquation.Callback 0#u64 (part,FJb_LimbMap.words x)
    let q ← state_only_poseidon.extension_from_raw_limbs zero
    let s1 ← Array.update s 0#usize q
    ok (s1,full))=ok (s1,full)
  rw [rp,bind_tc_ok,rf,bind_tc_ok,rz,bind_tc_ok,rq,bind_tc_ok,rs,bind_tc_ok]
#print axioms success
end AspisR1.JGj_InternalPrepare
end
