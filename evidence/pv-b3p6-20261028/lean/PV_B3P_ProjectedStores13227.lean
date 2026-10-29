import PV_B3P_ProjectedCell130227
import PV_B3P_ProjectedCell131227
import PV_B3P_ProjectedCell132227
import PV_B3P_ProjectedCell133227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false
attribute [local irreducible] projected_compute13

theorem projected_values13
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (leading full : Array aspis_core.field.QM31 4#usize)
    (internal : Array aspis_core.field.QM31 16#usize)
    (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) :
    projected_stage13_0 openings leading full internal pqm pqm1 pqm2 prepared_block =
      four_values13 (projected_compute13 openings leading full internal pqm pqm1 pqm2 prepared_block) := by
  rw [projected_cell_binding13_0]
  unfold four_values13
  apply congrArg (Aeneas.Std.bind _)
  funext a
  rw [projected_cell_binding13_1]
  apply congrArg (Aeneas.Std.bind _)
  funext b
  rw [projected_cell_binding13_2]
  apply congrArg (Aeneas.Std.bind _)
  funext c
  exact projected_cell_binding13_3 openings leading full internal pqm pqm1 pqm2 prepared_block a b c

def projected_output_loop13
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (leading full : Array aspis_core.field.QM31 4#usize)
    (internal : Array aspis_core.field.QM31 16#usize)
    (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) :=
  slice_loop13
    (slice_store13 (projected_compute13 openings leading full internal pqm pqm1 pqm2 prepared_block))
    (Array.make 4#usize [aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,
      aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO])

theorem projected_output_loop_binding13
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (leading full : Array aspis_core.field.QM31 4#usize)
    (internal : Array aspis_core.field.QM31 16#usize)
    (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) :
    projected_output_loop13 openings leading full internal pqm pqm1 pqm2 prepared_block =
      projected_stage13_0 openings leading full internal pqm pqm1 pqm2 prepared_block := by
  unfold projected_output_loop13
  rw [slice_four_literal13]
  exact (projected_values13 openings leading full internal pqm pqm1 pqm2 prepared_block).symm
#print axioms projected_values13
#print axioms projected_output_loop_binding13
end PV_B3P_Binding13227
