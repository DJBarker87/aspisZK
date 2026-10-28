import NDE_PackedAfterTotal
import NDE_PackedOuter
import RPv_FJe_PackedRawValue
import NDE_Map
set_option autoImplicit false
noncomputable section
namespace AspisR1.NDE_PackedTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical)
theorem source (input : Array NQ 4#usize) (hc : canonical input) :
    ∃ out,state_only_poseidon.external_local_packed_raw input=ok out := by
  obtain ⟨mapped,hm,_⟩ := NDE_Map.source
    (BuiltinFnMut NQ (Array U32 4#usize)) (fun _=>True) input state_only_poseidon.extension_limbs (by
      intro x hx
      exact ⟨FJb_LimbMap.words x,rfl,True.intro⟩)
  have em := FJb_LimbMap.value input mapped hm
  obtain ⟨table,ht⟩ := FJe_PackedRawTable.total mapped
  obtain ⟨bound,hb,vb,hw⟩ := FJe_PackedBound.value
  have vt := FJe_PackedRawTable.value mapped table ht
  have bounded : ∀ r j,(FJe_PackedRawAfter.words table r j).val<bound.val := by
    intro r j
    change (FJb_TailCell.cell (FJb_TailCell.cell table r) j).val<bound.val
    rw [vt r j,vb,em]
    exact FJe_RawReference.row_bounds _ (FJe_PackedInputWords.bounded input hc) r j
  obtain ⟨out,ho⟩ := NDE_PackedAfterTotal.source table bound bounded hw
  refine ⟨out,?_⟩
  unfold state_only_poseidon.external_local_packed_raw
  change (do
    let mapped ← core.array.Array.map (BuiltinFnMut NQ (Array U32 4#usize)) input state_only_poseidon.extension_limbs
    let table ← FJe_PackedRawTable.construct mapped
    let _ ← state_only_poseidon.external_local_packed_raw_loop0 table true 0#usize
    let bound ← state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
    FJe_PackedRawAfter.source table bound)=ok out
  have hmNative : core.array.Array.map (BuiltinFnMut NQ (Array U32 4#usize)) input state_only_poseidon.extension_limbs=ok mapped := hm
  rw [hmNative,bind_tc_ok,ht,bind_tc_ok,NDE_PackedOuter.source 4 table true 0#usize rfl,bind_tc_ok,hb,bind_tc_ok,ho]
#print axioms source
end AspisR1.NDE_PackedTotal
end
