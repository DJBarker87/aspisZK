import AspisR364ControlFlowPattern.Funs

namespace AspisR367ControlFlowExecution

abbrev Target := AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_a0c72fd3c47f69cbec0a6fc726dbdebb
abbrev InnerResidual := AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_042548220a408ec1acda44bb0b2e0d90
abbrev OuterResult := AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_4c2587ef7509c1eeb3f57d3aa5f3dc08

 theorem branch_exact (x : Target) :
    AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_a0c72fd3c47f69cbec0a6fc726dbdebb.Insts.CoreOpsTry_traitTry.branch x =
      .ok (match x with
        | .Continue _ => AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_4c2587ef7509c1eeb3f57d3aa5f3dc08.Continue ()
        | .Break _ => AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_4c2587ef7509c1eeb3f57d3aa5f3dc08.Break
          (AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_042548220a408ec1acda44bb0b2e0d90.Break ())) := by
  cases x <;> rfl

 theorem from_output_exact (u : Unit) :
    AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_a0c72fd3c47f69cbec0a6fc726dbdebb.Insts.CoreOpsTry_traitTry.from_output u =
      .ok (AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_a0c72fd3c47f69cbec0a6fc726dbdebb.Continue ()) := by
  cases u
  rfl

 theorem from_residual_exact (r : InnerResidual) :
    AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_a0c72fd3c47f69cbec0a6fc726dbdebb.Insts.CoreOpsTry_traitFromResidualControlFlow.from_residual r =
      .ok (AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_a0c72fd3c47f69cbec0a6fc726dbdebb.Break ()) := by
  cases r with
  | Continue impossible => cases impossible
  | Break u0 =>
    simp [AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_a0c72fd3c47f69cbec0a6fc726dbdebb.Insts.CoreOpsTry_traitFromResidualControlFlow.from_residual,
      Aeneas.Std.read_discriminant,
      AspisR364ControlFlowPattern.core.ops.control_flow.ControlFlow_mono_042548220a408ec1acda44bb0b2e0d90.read_discriminant,
      Aeneas.Std.massert]

#print axioms branch_exact
#print axioms from_output_exact
#print axioms from_residual_exact

end AspisR367ControlFlowExecution
