import RPu_FJn_GatherValue
import RPu_FJn_ClaimsModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_GatherProjection
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K decode)
/-- Read the original width29 row; source gather drops only each last column. -/
def claims (c : FIr_GatherCallback.Claims) : Fin 3 → Fin 29 → K := fun j l=>
  let row:=c.val[j.val]'(by rw [c.property];exact j.isLt)
  FIv_NativeArray.value row l.val
/-- Source row/column division is exact below the selected width28. -/
theorem cell (c : FIr_GatherCallback.Claims) (j : Fin 3) (l : Fin 29) (hl : l.val<28) :
    FJn_GatherCell.value c (j.val*28+l.val)=claims c j l := by
  have div : (j.val*28+l.val)/28=j.val := by omega
  have rem : (j.val*28+l.val)%28=l.val := by omega
  simp only [FJn_GatherCell.value,div,rem,claims,
    List.getElem?_eq_getElem (by rw [c.property];exact j.isLt)]
/-- Complete gather transport on precisely the cells consumed by the terminal. -/
theorem value (c : FIr_GatherCallback.Claims) (out : Array field.QM31 84#usize)
    (run : array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      FIr_GatherCanonical.callback field.QM31.ZERO c=ok out)
    (j : Fin 3) (l : Fin 29) (hl : l.val<28) :
    FJn_ClaimsModel.claims out j l=claims c j l := by
  have bound : j.val*28+l.val<84 := by omega
  have v:=congrFun (FJn_GatherValue.value c out run) ⟨j.val*28+l.val,bound⟩
  rw [←FJk_CopyRowTransport.cell out ⟨j.val*28+l.val,bound⟩] at v
  exact v.trans (cell c j l hl)
#print axioms cell
#print axioms value
end AspisR1.FJn_GatherProjection
end
