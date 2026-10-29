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
theorem projected_cell_binding13_0 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (leading full : Array aspis_core.field.QM31 4#usize) (internal : Array aspis_core.field.QM31 16#usize) (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) :
    projected_stage13_0 openings leading full internal pqm pqm1 pqm2 prepared_block  = (do
      let value ← projected_compute13 openings leading full internal pqm pqm1 pqm2 prepared_block 0#usize
      projected_stage13_1 openings leading full internal pqm pqm1 pqm2 prepared_block value) := by
  unfold projected_stage13_0 projected_compute13
  simp only [PV_B3P_Ordered227.bind_assoc,PV_B3P_Binding12227.bind_return12]
  apply congrArg (Aeneas.Std.bind _)
  funext start
  apply congrArg (Aeneas.Std.bind _)
  funext i
  apply congrArg (Aeneas.Std.bind _)
  funext q18
  apply congrArg (Aeneas.Std.bind _)
  funext i1
  apply congrArg (Aeneas.Std.bind _)
  funext q19
  apply congrArg (Aeneas.Std.bind _)
  funext i2
  apply congrArg (Aeneas.Std.bind _)
  funext q20
  apply congrArg (Aeneas.Std.bind _)
  funext i3
  apply congrArg (Aeneas.Std.bind _)
  funext q21
  apply congrArg (Aeneas.Std.bind _)
  funext s
  apply congrArg (Aeneas.Std.bind _)
  funext target
  apply congrArg (Aeneas.Std.bind _)
  funext i4
  apply congrArg (Aeneas.Std.bind _)
  funext q22
  apply congrArg (Aeneas.Std.bind _)
  funext i5
  apply congrArg (Aeneas.Std.bind _)
  funext q23
  apply congrArg (Aeneas.Std.bind _)
  funext i6
  apply congrArg (Aeneas.Std.bind _)
  funext q24
  apply congrArg (Aeneas.Std.bind _)
  funext i7
  apply congrArg (Aeneas.Std.bind _)
  funext q25
  apply congrArg (Aeneas.Std.bind _)
  funext s1
  apply congrArg (Aeneas.Std.bind _)
  funext internal1
  apply congrArg (Aeneas.Std.bind _)
  funext q26
  apply congrArg (Aeneas.Std.bind _)
  funext q27
  apply congrArg (Aeneas.Std.bind _)
  funext q28
  apply congrArg (Aeneas.Std.bind _)
  funext q29
  apply congrArg (Aeneas.Std.bind _)
  funext q30
  apply congrArg (Aeneas.Std.bind _)
  funext q31
  apply congrArg (Aeneas.Std.bind _)
  funext q32
  rfl
#print axioms projected_cell_binding13_0
end PV_B3P_Binding13227
