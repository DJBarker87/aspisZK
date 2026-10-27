import PV_B3_LinearsFinite
namespace PV_B3_Mask117Finite
open Aeneas Aeneas.Std Result PV_B3_Copy_117
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
 def linears (point : Array Q 10#usize) : Result (Q×Q) := do
  let (suffix,weighted) ← PV_B3_BoundedLoop.bounded (PV_B3_LinearsFinite.body point) 10
    (aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,10#usize)
  let q ← aspis_core.field.QM31.mul_m31 suffix 3#u32
  let q1 ← aspis_core.field.QM31.mul_m31 weighted 22#u32
  let q2 ← aspis_core.field.QM31.add q q1
  let q3 ← aspis_core.field.QM31.mul_m31 suffix 275#u32
  let q4 ← aspis_core.field.QM31.mul_m31 weighted 150#u32
  let q5 ← aspis_core.field.QM31.add q3 q4
  ok (q2,q5)
 theorem linears_source (point : Array Q 10#usize) :
    host_arithmetic.selected_mask_linears point = linears point := by
  unfold host_arithmetic.selected_mask_linears linears
  rw [PV_B3_LinearsFinite.source]
  unfold aspis_core.state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS
  rfl
 def reference (c1 : Array Q 16#usize) (mask : Array Q 10#usize) (g : Q)
    (point : Array Q 10#usize) : Result Q := do
  let (linear,explicit_linear) ← linears point
  let coefficients ← host_arithmetic.selected_coefficients c1
  let coefficients1 ← host_arithmetic.mask_only_coefficients coefficients mask
  let shared ← host_arithmetic.selected_horner coefficients1 linear
  let q ← host_arithmetic.mask_power_26 explicit_linear
  let q1 ← aspis_core.field.QM31.add aspis_core.field.QM31.ONE q
  let q2 ← aspis_core.field.QM31.mul q1 g
  aspis_core.field.QM31.add shared q2
 theorem source_complete (c1 : Array Q 16#usize) (mask : Array Q 10#usize) (g : Q)
    (point : Array Q 10#usize) :
    host_arithmetic.state_only_selected_mask_value c1 mask g point = reference c1 mask g point := by
  unfold host_arithmetic.state_only_selected_mask_value reference
  rw [linears_source]
#print axioms linears
#print axioms linears_source
#print axioms reference
#print axioms source_complete
end PV_B3_Mask117Finite
