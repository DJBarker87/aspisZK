import FJe_PackedRawRowValue
import FJb_BuilderTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedRawRow
open Aeneas Aeneas.Std Result FIq_Native
open FJb_RawRowCallbacks (Input)
open FJb_TailCell (cell)
abbrev inner := state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
abbrev outer := state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
abbrev Row := Array U64 4#usize
theorem total (input : Input) (r : Usize) (hr : r.val<4) :
    ∃ row : Row,array_from_fn_copy 4#usize core.marker.CopyU64 inner 0#u64 (input,r)=ok row := by
  apply FJb_BuilderTotal.value
  intro i hi
  exact FJe_PackedRawCallbacks.total input r i hr hi

theorem value (input : Input) (r : Usize) (hr : r.val<4) (row : Row)
    (run : array_from_fn_copy 4#usize core.marker.CopyU64 inner 0#u64 (input,r)=ok row) :
    ∀ j : Fin 4,(cell row j).val=RawPoseidonExternalRows.rawRowNat
      (fun k=>FJe_PackedRawRowValue.words input k j) ⟨r.val,hr⟩ := by
  have selected := FJb_BuilderSelected.value 4#usize core.marker.CopyU64 inner 0#u64
    (input,r) (by intro i hi;exact FJe_PackedRawCallbacks.total input r i hr hi) row run
  intro j
  let i : Usize := Usize.ofNatCore j.val (lt_trans j.isLt (4#usize).hBounds)
  have vi : i.val=j.val := by simp [i]
  have hi : i.val<4 := by rw [vi];exact j.isLt
  have hiArray : i.val<(4#usize).val := by change i.val<4;exact hi
  have ri := selected i hiArray
  have v := FJe_PackedRawRowValue.value input r i hr hi
    (row.val[i.val]'(by rw [row.property];exact hiArray)) ri
  simpa only [cell,vi] using v

theorem callback_total (input : Input) (r : Usize) (hr : r.val<4) :
    ∃ row : Row,outer.call_mut input r=ok (row,input) := by
  obtain ⟨row,rr⟩ := total input r hr
  refine ⟨row,?_⟩
  simp only [outer,
    state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut,
    rr,bind_tc_ok]

theorem callback_value (input : Input) (r : Usize) (hr : r.val<4) (row : Row)
    (run : outer.call_mut input r=ok (row,input)) :
    ∀ j : Fin 4,(cell row j).val=RawPoseidonExternalRows.rawRowNat
      (fun k=>FJe_PackedRawRowValue.words input k j) ⟨r.val,hr⟩ := by
  change (do
    let actual ← array_from_fn_copy 4#usize core.marker.CopyU64 inner 0#u64 (input,r)
    ok (actual,input))=ok (row,input) at run
  obtain ⟨actual,called,run⟩ := FIv_Map.bind_success _ _ _ run
  have same : actual=row := congrArg Prod.fst (Result.ok.inj run)
  subst actual
  exact value input r hr row called
#print axioms total
#print axioms value
#print axioms callback_total
#print axioms callback_value
end AspisR1.FJe_PackedRawRow
end
