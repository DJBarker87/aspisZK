import NHU_COMBINED_IMPORT
import RPv_JFy_SelectorRow
import RPv_FIw_SelectorRow
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_SelectorRow
open FIq_Native.pool_v1.pair_forest_copy_terminal
/-- Native operand-domain premises follow on this SAME selected record. -/
theorem operands (s : Selectors) (row : Usize) (bound : row.val<1024)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ index high low,
 Array.index_usize s.high index=ok high ∧ index.val=row.val/16 ∧
 Array.index_usize s.low (row &&& 15#usize)=ok low ∧
 FIv_NativeValue.Canon high ∧ FIv_NativeValue.Canon low := by
 obtain ⟨index,shift,value⟩:=FIw_SelectorIndices.high row
 obtain ⟨high,read,canonical⟩:=JFy_ArrayTotal.read s.high index (by change index.val<64;omega) hh
 obtain ⟨low,readlow,lc⟩:=JFy_ArrayTotal.read s.low (row &&& 15#usize) (by rw [FIw_SelectorIndices.low];omega) hl
 exact ⟨index,high,low,read,value,readlow,canonical,lc⟩
/-- Complete emitted helper, no successful result or independently selected product premise. -/
theorem result (s : Selectors) (row : Usize) (bound : row.val<1024)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ out, Selectors.row s row=ok out ∧ FIv_NativeValue.Canon out ∧
 FIv_NativeValue.decode out=FIv_NativeArray.value s.high (row.val/16)*
 FIv_NativeArray.value s.low (row.val%16) := by
 obtain ⟨out,run,_⟩:=WP.spec_imp_exists (JFy_SelectorRow.source s row bound hh hl)
 exact ⟨out,run,FIw_SelectorRow.value_exact s row out hh hl run⟩
#print axioms operands
#print axioms result
end AspisR1.NIH_SelectorRow
end
