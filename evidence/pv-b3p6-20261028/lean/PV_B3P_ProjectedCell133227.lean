import PV_B3P_ProjectedCompute13227
import PV_B3P_P227_14
import PV_B3P_Operations12227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding12227 Result
set_option autoImplicit false
attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub
  aspis_core.field.QM31.mul reference_field.qm31_pack_base4
  reference_field.qm31_sum_products3_prepared reference_field.PreparedQm31Multiplier.mul
  reference_field.PreparedQm31Multiplier.new reference_poseidon.interpolated_full_pair_packed
  reference_poseidon.interpolated_internal_pair reference_poseidon.leading_pair_packed
theorem projected_cell_binding13_3 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (leading full : Array aspis_core.field.QM31 4#usize) (internal : Array aspis_core.field.QM31 16#usize) (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) (q32 q47 q62 : aspis_core.field.QM31) :
    projected_stage13_3 openings leading full internal pqm pqm1 pqm2 prepared_block q32 q47 q62 = (do
      let value ← projected_compute13 openings leading full internal pqm pqm1 pqm2 prepared_block 3#usize
      .ok (Array.make 4#usize [q32,q47,q62,value])) := by
  unfold projected_stage13_3 projected_compute13
  simp only [PV_B3P_Ordered227.bind_assoc,PV_B3P_Binding12227.bind_return12]
  apply congrArg (Aeneas.Std.bind _)
  funext start3
  apply congrArg (Aeneas.Std.bind _)
  funext i24
  apply congrArg (Aeneas.Std.bind _)
  funext q63
  apply congrArg (Aeneas.Std.bind _)
  funext i25
  apply congrArg (Aeneas.Std.bind _)
  funext q64
  apply congrArg (Aeneas.Std.bind _)
  funext i26
  apply congrArg (Aeneas.Std.bind _)
  funext q65
  apply congrArg (Aeneas.Std.bind _)
  funext i27
  apply congrArg (Aeneas.Std.bind _)
  funext q66
  apply congrArg (Aeneas.Std.bind _)
  funext s6
  apply congrArg (Aeneas.Std.bind _)
  funext target3
  apply congrArg (Aeneas.Std.bind _)
  funext i28
  apply congrArg (Aeneas.Std.bind _)
  funext q67
  apply congrArg (Aeneas.Std.bind _)
  funext i29
  apply congrArg (Aeneas.Std.bind _)
  funext q68
  apply congrArg (Aeneas.Std.bind _)
  funext i30
  apply congrArg (Aeneas.Std.bind _)
  funext q69
  apply congrArg (Aeneas.Std.bind _)
  funext i31
  apply congrArg (Aeneas.Std.bind _)
  funext q70
  apply congrArg (Aeneas.Std.bind _)
  funext s7
  apply congrArg (Aeneas.Std.bind _)
  funext internal4
  apply congrArg (Aeneas.Std.bind _)
  funext q71
  apply congrArg (Aeneas.Std.bind _)
  funext q72
  apply congrArg (Aeneas.Std.bind _)
  funext q73
  apply congrArg (Aeneas.Std.bind _)
  funext q74
  apply congrArg (Aeneas.Std.bind _)
  funext q75
  apply congrArg (Aeneas.Std.bind _)
  funext q76
  apply congrArg (Aeneas.Std.bind _)
  funext q77
  rfl
#print axioms projected_cell_binding13_3
end PV_B3P_Binding13227
