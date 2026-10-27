import JFy_Specs
import JFy_Lift
import JFy_SelectorRow
import JFy_Scalars
attribute [step] AspisR1.JFy_Specs.add AspisR1.JFy_Specs.mul AspisR1.JFy_Specs.sub
  AspisR1.JFy_Specs.square AspisR1.JFy_Specs.pow5 AspisR1.JFy_Specs.read AspisR1.JFy_Specs.update
  AspisR1.JFy_Lift.semantic AspisR1.JFy_Lift.copy AspisR1.JFy_SelectorRow.source
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_Steps
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal
@[step] theorem scalars (v : CompiledVariant) (present : Bool) (a b c d : field.QM31)
    (ha : Canon a) (hb : Canon b) (hc : Canon c) (hd : Canon d) :
    scalar_lanes v present a b c d ⦃ out => canonical out ⦄ := by
  apply exists_imp_spec
  exact JFy_Scalars.source v present a b c d ha hb hc hd
#print axioms scalars
end AspisR1.JFy_Steps
end
