import PV_B3P_Success227
import PV_B3P_E227_18
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_field_cm31_mul_r (value : aspis_core.field.CM31) :
    Success (reference_field.cm31_mul_r value) := by
  unfold reference_field.cm31_mul_r
  apply bind
  · apply double
  intro m
  apply bind
  · apply sub
  intro m1
  apply bind
  · apply double
  intro m2
  apply bind
  · apply add
  intro m3
  apply cnew

#print axioms total_reference_field_cm31_mul_r

theorem total_reference_field_prepare_component (component : aspis_core.field.CM31) :
    Success (reference_field.prepare_component component) := by
  unfold reference_field.prepare_component
  apply bind
  · apply add
  intro m
  exact ok _

#print axioms total_reference_field_prepare_component

theorem total_reference_field_prepared_component_mul (left : Array aspis_core.field.M31 3#usize) (right : aspis_core.field.CM31) :
    Success (reference_field.prepared_component_mul left right) := by
  unfold reference_field.prepared_component_mul
  apply bind
  · apply index <;> scalar_tac
  intro m
  apply bind
  · apply mul
  intro m0
  apply bind
  · apply index <;> scalar_tac
  intro m1
  apply bind
  · apply mul
  intro m11
  apply bind
  · apply index <;> scalar_tac
  intro m2
  apply bind
  · apply add
  intro m3
  apply bind
  · apply mul
  intro m21
  apply bind
  · apply sub
  intro m4
  apply bind
  · apply sub
  intro m5
  apply bind
  · apply sub
  intro m6
  exact ok _

#print axioms total_reference_field_prepared_component_mul

theorem total_reference_field_PreparedQm31Multiplier_new (value : aspis_core.field.QM31) :
    Success (reference_field.PreparedQm31Multiplier.new value) := by
  unfold reference_field.PreparedQm31Multiplier.new
  apply bind
  · apply total_reference_field_prepare_component
  intro a
  apply bind
  · apply total_reference_field_prepare_component
  intro a1
  apply bind
  · apply cadd
  intro c
  apply bind
  · apply total_reference_field_prepare_component
  intro a2
  exact ok _

#print axioms total_reference_field_PreparedQm31Multiplier_new

theorem total_reference_field_PreparedQm31Multiplier_mul (self : reference_field.PreparedQm31Multiplier) (rhs : aspis_core.field.QM31) :
    Success (reference_field.PreparedQm31Multiplier.mul self rhs) := by
  unfold reference_field.PreparedQm31Multiplier.mul
  apply bind
  · apply index <;> scalar_tac
  intro a
  apply bind
  · apply total_reference_field_prepared_component_mul
  intro m0
  apply bind
  · apply index <;> scalar_tac
  intro a1
  apply bind
  · apply total_reference_field_prepared_component_mul
  intro m1
  apply bind
  · apply index <;> scalar_tac
  intro a2
  apply bind
  · apply cadd
  intro c
  apply bind
  · apply total_reference_field_prepared_component_mul
  intro m2
  apply bind
  · apply total_reference_field_cm31_mul_r
  intro c1
  apply bind
  · apply cadd
  intro c2
  apply bind
  · apply csub
  intro c3
  apply bind
  · apply csub
  intro c4
  exact ok _

#print axioms total_reference_field_PreparedQm31Multiplier_mul

theorem total_reference_field_reconstruct_component (channels : Array Std.U64 3#usize) :
    Success (reference_field.reconstruct_component channels) := by
  unfold reference_field.reconstruct_component
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply bind
  · apply reduce64
  intro m0
  apply bind
  · apply index <;> scalar_tac
  intro i1
  apply bind
  · apply reduce64
  intro m1
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply bind
  · apply reduce64
  intro m2
  apply bind
  · apply sub
  intro m
  apply bind
  · apply sub
  intro m3
  apply bind
  · apply sub
  intro m4
  exact ok _

#print axioms total_reference_field_reconstruct_component

theorem total_reference_field_terminal_limb (value : aspis_core.field.M31) :
    Success (reference_field.terminal_limb value) := by
  unfold reference_field.terminal_limb
  exact ok _

#print axioms total_reference_field_terminal_limb

end PV_B3P_Success227
