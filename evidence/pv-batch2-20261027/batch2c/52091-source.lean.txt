import R1Z.PV_B2_C_EmissionProbe
set_option autoImplicit false
namespace PV_B2_C_FullEmissionProbe
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_EmissionProbe
/-- All 1024 updated values, retaining the complete success/failure Result. -/
def probe (v : transport.Variant) : Result (Bool × List (List Nat)) := do
  let (status,out) ← pv_b2_materialize (weights v)
    aspis_core.field.wide_exact.WideExact.ONE
    (Array.repeat 1024#usize aspis_core.field.wide_exact.WideExact.ZERO)
  ok ((match status with | .Ok _ => true | .Err _ => false),out.val.map limbs)
#eval probe .S1
#eval probe .S2
#eval probe .D
#print axioms probe
end PV_B2_C_FullEmissionProbe
