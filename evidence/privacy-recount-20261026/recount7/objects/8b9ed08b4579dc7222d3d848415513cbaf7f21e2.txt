import PV_B3_Range117
namespace PV_B3_Mask117RangeSource
open Aeneas Aeneas.Std Result PV_B3_Copy_117
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31

def reference (c1 : Array Q 16#usize) (mask : Array Q 10#usize)
    (g : Q) (point : Array Q 10#usize) : Result Q := do
  let (linear, explicit_linear) ← host_arithmetic.selected_mask_linears point
  let coefficients ← PV_B3_Range117.scatter c1 host_arithmetic.FACTOR_EXPONENTS
    PV_B3_Range117.selectedIndices (Array.repeat 27#usize aspis_core.field.QM31.ZERO)
  let coefficients ← PV_B3_Range117.scatter mask host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
    PV_B3_Range117.maskIndices coefficients
  let shared ← (do
    let prepared ← host_arithmetic.PreparedQm31Multiplier.new linear
    let shared ← Array.index_usize coefficients
      aspis_core.state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE
    PV_B3_Range117.horner coefficients prepared PV_B3_Range117.hornerIndices shared)
  let power ← host_arithmetic.mask_power_26 explicit_linear
  let factor ← aspis_core.field.QM31.add aspis_core.field.QM31.ONE power
  let explicit ← aspis_core.field.QM31.mul factor g
  aspis_core.field.QM31.add shared explicit

theorem source (c1 : Array Q 16#usize) (mask : Array Q 10#usize)
    (g : Q) (point : Array Q 10#usize) :
    host_arithmetic.state_only_selected_mask_value c1 mask g point =
      reference c1 mask g point := by
  unfold host_arithmetic.state_only_selected_mask_value reference
  simp_rw [PV_B3_Range117.selected, PV_B3_Range117.mask_only,
    PV_B3_Range117.prepared_horner]

#print axioms reference
#print axioms source
end PV_B3_Mask117RangeSource
