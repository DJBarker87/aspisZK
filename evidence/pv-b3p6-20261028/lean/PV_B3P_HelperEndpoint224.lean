import PV_B3P_Emission224
import PV_B3P_HelperEffects224
namespace PV_B3P_HelperEndpoint224
open Aeneas Aeneas.Std PV_B3P_224 PV_B3P_HelperEffects224
set_option autoImplicit false

def operations : Operations aspis_core.field.QM31 aspis_core.field.M31 reference224.Error :=
  { zero := aspis_core.field.QM31.ZERO
    active := fun w => decide (w ≠ aspis_core.field.M31.ZERO)
    sub := aspis_core.field.QM31.sub
    inverse := aspis_core.field.QM31.try_inv
    weighted := aspis_core.field.QM31.mul_m31
    add := aspis_core.field.QM31.add
    imbalance := reference224.Error.CopyImbalance }

-- Arithmetic calls stay symbolic; all failure and divergence paths are kept.
theorem source (value operand : aspis_core.field.QM31) (weight : aspis_core.field.M31)
    (chi : aspis_core.field.QM31) (consumer : Bool) :
    reference224.endpoint value operand weight chi consumer =
      endpoint operations consumer chi value operand weight := by
  simp only [reference224.endpoint,aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,bind_tc_ok,
    endpoint,operations]
  by_cases h : weight = aspis_core.field.M31.ZERO <;> simp [h]
  all_goals
    intros
    cases consumer <;> rfl

#print axioms source
end PV_B3P_HelperEndpoint224
