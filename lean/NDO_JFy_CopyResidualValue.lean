import RPv_JFy_CopyResidual
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_CopyResidualValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem source (r : CopyRowExtension) (helper chi : field.QM31)
    (hpv : canonical r.producer_values) (hcv : canonical r.consumer_values)
    (hpw : canonical r.producer_weights) (hcw : canonical r.consumer_weights)
    (hh : Canon helper) (hc : Canon chi) :
    ∃ out,copy_residual r helper chi=ok out ∧ Canon out ∧
      decode out=FIw_CopyMeaning.residual r (decode helper) (decode chi) := by
  obtain ⟨out,call,hout⟩ := JFy_CopyResidual.source r helper chi hpv hcv hpw hcw hh hc
  exact ⟨out,call,FIw_CopyMeaning.value_exact r helper chi out hpv hcv hpw hcw hh hc call⟩
#print axioms source
end AspisR1.JFy_CopyResidualValue
end
