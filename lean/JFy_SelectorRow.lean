import JFy_Specs
import FIq_Native13
import FIw_SelectorIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SelectorRow
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

@[spec] theorem source (s : Selectors) (row : Usize) (bound : row.val<1024)
    (hh : canonical s.high) (hl : canonical s.low) :
    Selectors.row s row ⦃ out => Canon out ⦄ := by
  obtain ⟨i,shift,hiv⟩ := FIw_SelectorIndices.high row
  obtain ⟨high,hhcall,hhc⟩ := JFy_ArrayTotal.read s.high i (by change i.val<64;omega) hh
  have lobound : (row &&& 15#usize).val<16 := by rw [FIw_SelectorIndices.low];omega
  obtain ⟨low,hlcall,hlc⟩ := JFy_ArrayTotal.read s.low (row &&& 15#usize) lobound hl
  obtain ⟨out,hout,hc,_⟩ := JFy_FieldTotal.mul high low hhc hlc
  have call : Selectors.row s row=ok out := by
    unfold Selectors.row
    rw [shift,bind_tc_ok,hhcall,bind_tc_ok]
    simp only [lift,bind_tc_ok]
    rw [hlcall,bind_tc_ok,hout]
  rw [call]
  exact hc
#print axioms source
end AspisR1.JFy_SelectorRow
end
