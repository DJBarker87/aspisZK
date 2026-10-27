import JFy_Specs
import FIq_Native13
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_Lift
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)

@[spec] theorem semantic (x : U32) (hx : x.val<2147483647) :
    pool_v1.pair_forest_semantic_terminal.lift_m31 x ⦃ out => Canon out ⦄ := by
  unfold pool_v1.pair_forest_semantic_terminal.lift_m31 field.CM31.from_m31 field.QM31.from_cm31
  simp only [bind_tc_ok]
  change (x.val<2147483647 ∧ 0<2147483647) ∧ (0<2147483647 ∧ 0<2147483647)
  exact ⟨⟨hx,by omega⟩,by omega,by omega⟩
#print axioms semantic
@[spec] theorem copy (x : U32) (hx : x.val<2147483647) :
    pool_v1.pair_forest_copy_terminal.lift_m31 x ⦃ out => Canon out ⦄ := by
  exact semantic x hx
#print axioms copy
end AspisR1.JFy_Lift
end
