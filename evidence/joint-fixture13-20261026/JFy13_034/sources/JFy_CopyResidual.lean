import JFy_Specs
import FIw_CopyMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_CopyResidual
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem source (r : CopyRowExtension) (helper chi : field.QM31)
    (hpv : canonical r.producer_values) (hcv : canonical r.consumer_values)
    (hpw : canonical r.producer_weights) (hcw : canonical r.consumer_weights)
    (hh : Canon helper) (hc : Canon chi) :
    ∃ out,copy_residual r helper chi=ok out ∧ Canon out := by
  have spec : copy_residual r helper chi ⦃ out => Canon out ⦄ := by
    unfold copy_residual
    step* <;> first | assumption | scalar_tac
  exact WP.spec_imp_exists spec
#print axioms source
end AspisR1.JFy_CopyResidual
end
