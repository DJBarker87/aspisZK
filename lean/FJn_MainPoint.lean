import FIr_CarrierCanonical
import FJk_CopyRowTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MainPoint
open Aeneas Aeneas.Std
open FIq_Carriers (MQ mapArray toQ)
def point (a : Array MQ 10#usize) : Fin 10 → FIv_NativeValue.K := fun i=>
  FIp_SemanticValues.decode (a.val[i.val]'(by rw [a.property];exact i.isLt))
theorem value (a : Array MQ 10#usize) :
    FIw_ArrayValue.decoded (mapArray toQ a)=point a := by
  funext i
  unfold FIw_ArrayValue.decoded FIw_ArrayValue.cells mapArray point
  simp only [List.getElem_map]
  rfl
#print axioms value
end AspisR1.FJn_MainPoint
end
