import FJh_Base
import FIq_Native13
import R0P.Copy
set_option autoImplicit false
namespace AspisR1.FJk_ActiveMaskRegistry
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
/-- Static64-word registry equality;avoid nested Fin-case reduction. -/
theorem list : constants.ACTIVE_ROW_MASKS.val.map UScalar.val=List.ofFn R0P.copyActiveRowMasks := by
  unfold constants.ACTIVE_ROW_MASKS
  rfl
/-- Same actual stored mask at an arbitrary row. -/
theorem value (i : Fin 64) :
    (FJh_Base.cell constants.ACTIVE_ROW_MASKS i).val=R0P.copyActiveRowMasks i := by
  have hi : i.val<constants.ACTIVE_ROW_MASKS.val.length := by
    rw [constants.ACTIVE_ROW_MASKS.property]
    exact i.isLt
  have h := congrArg (fun xs : List Nat=>xs[i.val]?) list
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    List.getElem?_ofFn,dif_pos i.isLt,Option.some.injEq,FJh_Base.cell] using h
#print axioms list
#print axioms value
end AspisR1.FJk_ActiveMaskRegistry
