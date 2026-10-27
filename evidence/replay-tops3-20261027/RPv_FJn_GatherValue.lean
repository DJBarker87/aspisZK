import RPv_FJn_GatherCell
import RPv_FJk_OpeningSelected
import RPv_FIr_GatherCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_GatherValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (decode)
/-- Complete original84-cell gather VALUE, preserving actual row/column bytes. -/
theorem value (c : FIr_GatherCallback.Claims) (out : Array field.QM31 84#usize)
    (run : array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      FIr_GatherCanonical.callback field.QM31.ZERO c=ok out) :
    FIw_ArrayValue.decoded out=fun i=>FJn_GatherCell.value c i.val := by
  apply FJk_OpeningSelected.indices
  apply FIw_BuilderValue.fromFn 84#usize FIr_GatherCanonical.callback decode
    (fun c i=>FJn_GatherCell.value c i.val) _ c out run
  exact FJn_GatherCell.selected
#print axioms value
end AspisR1.FJn_GatherValue
end
