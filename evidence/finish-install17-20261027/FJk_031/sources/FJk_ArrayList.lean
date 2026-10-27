import FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_ArrayList
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)
open FIw_ArrayValue (decoded cells)
/-- Exact array-to-list interpretation, including the same stored cell order. -/
theorem value {N : Usize} (a : Array NQ N) :
    a.val.map decode=List.ofFn (decoded a) := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,a.property]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn]
    rfl
#print axioms value
end AspisR1.FJk_ArrayList
end
