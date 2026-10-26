import FIx_ArrayMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_ListDecoded
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)
open FIw_ArrayValue (decoded cells)

theorem value {N : Usize} (a : Array NQ N) (model : List K) (same : a.val.map decode=model)
    (i : Fin N.val) : decoded a i=(model[i.val]?).getD 0 := by
  have hi : i.val<a.val.length := by simpa only [a.property] using i.isLt
  rw [←same,List.getElem?_map,List.getElem?_eq_getElem hi]
  rfl
#print axioms value
end AspisR1.FIy_ListDecoded
end
