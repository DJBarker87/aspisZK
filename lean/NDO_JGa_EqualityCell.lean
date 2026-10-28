import RPv_JFy_Steps
import NDO_FIv_EqualityCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_EqualityCell
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)

@[step] theorem source (a b : field.QM31) (ha : Canon a) (hb : Canon b) :
    FIv_EqualityCell.call () (a,b) ⦃ out => Canon out ⦄ := by
  have one := FIv_NativeValue.one.1
  unfold FIv_EqualityCell.call pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
  step*
#print axioms source
end AspisR1.JGa_EqualityCell
end
