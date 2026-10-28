import NDE_Reference9.Funs
import RPu_FIq_Native08
import NDE_MulStubValue
import RPv_FIw_SelectorIndices
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NDE_RowBridge
abbrev Q := FIq_Native.field.QM31
abbrev Selectors := FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors
open NDE_MulStubValue (Canon words)

theorem read_total {α : Type} {n : Usize} (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    ∃ x, Array.index_usize a i = ok x ∧ a.val[i.val]? = some x := by
  have bound : i.val < a.val.length := by simpa only [a.property] using hi
  let x := a.val[i.val]'bound
  refine ⟨x,?_,List.getElem?_eq_getElem bound⟩
  unfold Array.index_usize
  simp only [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem bound]

theorem source_step (copy : core.marker.Copy Q) (s : Selectors) (row : Usize) :
    (do let pair ← NDE_Reference9.row_operands_ref copy s.high s.low row
        FIq_Native.field.QM31.mul pair.1 pair.2) =
    FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.row s row := by
  simp only [NDE_Reference9.row_operands_ref,
    FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.row,
    bind_assoc_eq,bind_tc_ok]

def SelectedCanon (s : Selectors) (row : Usize) : Prop :=
  (∀ x, s.high.val[row.val/16]? = some x → Canon x) ∧
  (∀ x, s.low.val[row.val%16]? = some x → Canon x)

theorem row_total (copy : core.marker.Copy Q) (s : Selectors) (row : Usize)
    (bound : row.val < 1024) (canon : SelectedCanon s row) :
    ∃ left right out,
      NDE_Reference9.row_operands_ref copy s.high s.low row = ok (left,right) ∧
      FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.row s row = ok out ∧
      Canon out ∧ words out = AspisR1.ExtractedMaskQM31Mul.qmMulWords (words left) (words right) := by
  obtain ⟨i,shift,value⟩ := AspisR1.FIw_SelectorIndices.high row
  obtain ⟨left,hl,slotl⟩ := read_total s.high i (by change i.val < 64; rw [value]; omega)
  obtain ⟨right,hr,slotr⟩ := read_total s.low (row &&& 15#usize)
    (by change (row &&& 15#usize).val < 16
        rw [AspisR1.FIw_SelectorIndices.low]
        exact Nat.mod_lt _ (by decide))
  have leftCanon := canon.1 left (by simpa only [value] using slotl)
  have rightCanon := canon.2 right (by simpa only [AspisR1.FIw_SelectorIndices.low] using slotr)
  have inputs : NDE_Reference9.row_operands_ref copy s.high s.low row = ok (left,right) := by
    simp only [NDE_Reference9.row_operands_ref,shift,hl,hr,lift,bind_tc_ok]
  obtain ⟨out,returned,hc,hv⟩ := NDE_MulStubValue.qm31_value left right leftCanon rightCanon
  refine ⟨left,right,out,inputs,?_,hc,hv⟩
  rw [← source_step copy s row,inputs,bind_tc_ok]
  exact returned

#print axioms read_total
#print axioms source_step
#print axioms row_total
end NDE_RowBridge
end
