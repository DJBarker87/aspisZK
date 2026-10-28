import PV_B3P_HelperEndpoint224
import PV_B3P_HelperIndex224
import PV_B3P_HelperOrder224
namespace PV_B3P_HelperRow224
open Aeneas Aeneas.Std PV_B3P_224 PV_B3P_RustResult PV_B3P_HelperIndex224
set_option autoImplicit false

def specification (r : aspis_statement.logup.CopyLogUpRow) (chi : aspis_core.field.QM31) :=
  PV_B3P_HelperEffects224.row PV_B3P_HelperEndpoint224.operations chi
    (zero r.producer_values,zero r.producer_weights)
    (one r.producer_values,one r.producer_weights)
    (zero r.consumer_values,zero r.consumer_weights)
    (one r.consumer_values,one r.consumer_weights)

set_option backward.isDefEq.respectTransparency false in
theorem complete_result (r : aspis_statement.logup.CopyLogUpRow) (chi : aspis_core.field.QM31) :
    reference224.one_row r chi = specification r chi := by
  rw [specification,PV_B3P_HelperOrder224.four_endpoints]
  unfold reference224.one_row
  simp only [index_zero,index_one,bind_tc_ok]
  rw [try_bind_eq]
  rw [PV_B3P_HelperEndpoint224.source]
  congr 1
  funext v0
  rw [try_bind_eq,PV_B3P_HelperEndpoint224.source]
  congr 1
  funext v1
  rw [try_bind_eq,PV_B3P_HelperEndpoint224.source]
  congr 1
  funext v2
  exact PV_B3P_HelperEndpoint224.source _ _ _ _ _

#print axioms complete_result
end PV_B3P_HelperRow224
