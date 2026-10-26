import FIw_SelectorIndices
import FIq_Native08
import FIv_NativeArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_SelectorRow
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIv_NativeArray (value)
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

theorem value_exact (selectors : Selectors) (row : Usize) (out : NQ)
    (hh : ∀ x∈selectors.high.val,Canon x) (hl : ∀ x∈selectors.low.val,Canon x)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.row selectors row=ok out) :
    Canon out ∧ decode out=value selectors.high (row.val/16)*value selectors.low (row.val%16) := by
  obtain ⟨index,shift,indexValue⟩ := FIw_SelectorIndices.high row
  unfold pool_v1.pair_forest_copy_terminal.Selectors.row at run
  rw [shift] at run
  simp only [bind_tc_ok,lift] at run
  obtain ⟨high,hhigh,r1⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨low,hlow,r2⟩ := FIv_Map.bind_success _ _ _ r1
  have hc := FIv_NativeArray.canonical selectors.high index high hh hhigh
  have lc := FIv_NativeArray.canonical selectors.low (row &&& 15#usize) low hl hlow
  have result := FIv_NativeValue.mul high low out hc lc r2
  refine ⟨result.1,?_⟩
  rw [result.2,← FIv_NativeArray.read selectors.high index high hhigh,
    ← FIv_NativeArray.read selectors.low (row &&& 15#usize) low hlow,indexValue,FIw_SelectorIndices.low]
#print axioms value_exact
end AspisR1.FIw_SelectorRow
end
