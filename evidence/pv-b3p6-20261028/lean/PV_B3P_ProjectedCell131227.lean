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
theorem projected_cell_binding13_1 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (leading full : Array aspis_core.field.QM31 4#usize) (internal : Array aspis_core.field.QM31 16#usize) (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) (q32 : aspis_core.field.QM31) :
    projected_stage13_1 openings leading full internal pqm pqm1 pqm2 prepared_block q32 = (do
      let value ← projected_compute13 openings leading full internal pqm pqm1 pqm2 prepared_block 1#usize
      projected_stage13_2 openings leading full internal pqm pqm1 pqm2 prepared_block q32 value) := by
  unfold projected_stage13_1 projected_compute13
  simp only [PV_B3P_Ordered227.bind_assoc,PV_B3P_Binding12227.bind_return12]
  apply congrArg (Aeneas.Std.bind _)
  funext start1
  apply congrArg (Aeneas.Std.bind _)
  funext i8
  apply congrArg (Aeneas.Std.bind _)
  funext q33
  apply congrArg (Aeneas.Std.bind _)
  funext i9
  apply congrArg (Aeneas.Std.bind _)
  funext q34
  apply congrArg (Aeneas.Std.bind _)
  funext i10
  apply congrArg (Aeneas.Std.bind _)
  funext q35
  apply congrArg (Aeneas.Std.bind _)
  funext i11
  apply congrArg (Aeneas.Std.bind _)
  funext q36
  apply congrArg (Aeneas.Std.bind _)
  funext s2
  apply congrArg (Aeneas.Std.bind _)
  funext target1
  apply congrArg (Aeneas.Std.bind _)
  funext i12
  apply congrArg (Aeneas.Std.bind _)
  funext q37
  apply congrArg (Aeneas.Std.bind _)
  funext i13
  apply congrArg (Aeneas.Std.bind _)
  funext q38
  apply congrArg (Aeneas.Std.bind _)
  funext i14
  apply congrArg (Aeneas.Std.bind _)
  funext q39
  apply congrArg (Aeneas.Std.bind _)
  funext i15
  apply congrArg (Aeneas.Std.bind _)
  funext q40
  apply congrArg (Aeneas.Std.bind _)
  funext s3
  apply congrArg (Aeneas.Std.bind _)
  funext internal2
  apply congrArg (Aeneas.Std.bind _)
  funext q41
  apply congrArg (Aeneas.Std.bind _)
  funext q42
  apply congrArg (Aeneas.Std.bind _)
  funext q43
  apply congrArg (Aeneas.Std.bind _)
  funext q44
  apply congrArg (Aeneas.Std.bind _)
  funext q45
  apply congrArg (Aeneas.Std.bind _)
  funext q46
  apply congrArg (Aeneas.Std.bind _)
  funext q47
  rfl
#print axioms projected_cell_binding13_1
end PV_B3P_Binding13227
