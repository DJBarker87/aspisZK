import RPv_FJe_PackedRawRow
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedRawTable
open Aeneas Aeneas.Std Result FIq_Native
open FJb_RawRowCallbacks (Input)
open FJb_TailCell (cell)
abbrev Table := Array (Array U64 4#usize) 4#usize
def construct (input : Input) : Result Table :=
  array_from_fn_copy 4#usize (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
    FJe_PackedRawRow.outer (Array.repeat 4#usize 0#u64) input

theorem total (input : Input) : ∃ table,construct input=ok table := by
  apply FJb_BuilderTotal.value
  intro r hr
  exact FJe_PackedRawRow.callback_total input r hr
/-- Complete original nested constructor table,from its SAME actual input. -/
theorem value (input : Input) (table : Table) (run : construct input=ok table) :
    ∀ r j : Fin 4,(cell (cell table r) j).val=RawPoseidonExternalRows.rawRowNat
      (fun k=>FJe_PackedRawRowValue.words input k j) r := by
  have selected := FJb_BuilderSelected.value 4#usize
    (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64) FJe_PackedRawRow.outer
    (Array.repeat 4#usize 0#u64) input
    (by intro r hr;exact FJe_PackedRawRow.callback_total input r hr) table run
  intro r j
  let i : Usize := Usize.ofNatCore r.val (lt_trans r.isLt (4#usize).hBounds)
  have vi : i.val=r.val := by simp [i]
  have hi : i.val<4 := by rw [vi];exact r.isLt
  have hiArray : i.val<(4#usize).val := by change i.val<4;exact hi
  have ri := selected i hiArray
  have v := FJe_PackedRawRow.callback_value input i hi
    (table.val[i.val]'(by rw [table.property];exact hiArray)) ri j
  simpa only [cell,vi] using v
#print axioms total
#print axioms value
end AspisR1.FJe_PackedRawTable
end
