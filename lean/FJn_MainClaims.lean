import FJn_GatherProjection
import FIr_CarrierCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MainClaims
open Aeneas Aeneas.Std
open FIq_Carriers (MQ mapArray toQ)
def claims (c : Array (Array MQ 29#usize) 3#usize) : Fin 3 → Fin 29 → FIv_NativeValue.K := fun j l=>
  let row:=c.val[j.val]'(by rw [c.property];exact j.isLt)
  FIp_SemanticValues.decode (row.val[l.val]'(by rw [row.property];exact l.isLt))
/-- The original main and native arrays share exactly the same claim limbs. -/
theorem value (c : Array (Array MQ 29#usize) 3#usize) (j : Fin 3) (l : Fin 29) :
    FJn_GatherProjection.claims (mapArray (mapArray toQ) c) j l=claims c j l := by
  unfold FJn_GatherProjection.claims claims
  simp only [mapArray,List.getElem_map]
  unfold FIv_NativeArray.value
  rw [List.getElem?_eq_getElem (by
    simp only [List.length_map]
    rw [(c.val[j.val]'(by rw [c.property];exact j.isLt)).property]
    exact l.isLt)]
  rfl
#print axioms value
end AspisR1.FJn_MainClaims
end
