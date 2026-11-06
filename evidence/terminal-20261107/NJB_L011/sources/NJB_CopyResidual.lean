import NIU_COMBINED_IMPORT
import NGK_COMBINED_IMPORT
import NDO_JFy_CopyResidualValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_CopyResidual
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal
/-- All eight row coordinates, helper and challenge belong to this SAME
invocation. Complete Result; all field-call laws are discharged internally. -/
theorem result (r : CopyRowExtension) (helper chi : field.QM31)
 (hpv : canonical r.producer_values) (hcv : canonical r.consumer_values)
 (hpw : canonical r.producer_weights) (hcw : canonical r.consumer_weights)
 (hh : Canon helper) (hc : Canon chi) :
 ∃ out, copy_residual r helper chi=ok out ∧ Canon out ∧
 decode out=FIw_CopyMeaning.residual r (decode helper) (decode chi) :=
 JFy_CopyResidualValue.source r helper chi hpv hcv hpw hcw hh hc
#print result
#print axioms result
end AspisR1.NJB_CopyResidual
end
