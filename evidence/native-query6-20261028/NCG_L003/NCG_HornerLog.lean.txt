import NCG_CallLog
set_option autoImplicit false
namespace NCG_HornerLog
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- Substitute the SAME three emitted products into the native log order.
All association premises are local primitive returns, not a whole fold return. -/
theorem three (alpha h0 h1 h2 h3 z0 z1 z2 t0 t1 out : Stage2E)
    (p0 : NBZ_Wide.product alpha h3 = ok z0)
    (a0 : NBO_FieldSemantics.add h2 z0 = ok t0)
    (p1 : NBZ_Wide.product alpha t0 = ok z1)
    (a1 : NBO_FieldSemantics.add h1 z1 = ok t1)
    (p2 : NBZ_Wide.product alpha t1 = ok z2)
    (a2 : NBO_FieldSemantics.add h0 z2 = ok out) :
    NBW_Horner.eval NBZ_Wide.product alpha [h0,h1,h2] h3 = ok out := by
  simp only [NBW_Horner.eval, bind_tc_ok, p0, a0, p1, a1, p2, a2]

#print axioms three
end NCG_HornerLog
