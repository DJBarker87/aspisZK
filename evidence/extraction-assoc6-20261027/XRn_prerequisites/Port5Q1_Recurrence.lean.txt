import OraclePortCheckpointResumeC5
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Recurrence
abbrev Model := OraclePortCheckpointStateC3.Prepared OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E
attribute [local irreducible] QueryAccumulator.run QueryAccumulator.run22 OraclePortCheckpointStateC3.advance

theorem ten (model : Model) :
    OraclePortCheckpointStateC3.advance model 10 QueryAccumulator.initial=
      (OraclePortCheckpointStateC3.write model).accumulator := by
  unfold OraclePortCheckpointStateC3.write
  have zero : QueryAccumulator.initial=QueryAccumulator.run model.iota model.rho
      (QueryAccumulator.extend22 model.values) (QueryAccumulator.extend22 model.basis) 0 := by
    rw [QueryAccumulator.run]
  rw [zero]
  exact OraclePortCheckpointStateC3.advance_run model 10 0

theorem twenty_two (model : Model) :
    OraclePortCheckpointStateC3.advance model 12 (OraclePortCheckpointStateC3.write model).accumulator=
      QueryAccumulator.run22 model.iota model.rho model.values model.basis := by
  unfold OraclePortCheckpointStateC3.write QueryAccumulator.run22
  exact OraclePortCheckpointStateC3.advance_run model 12 10

#print axioms ten
#print axioms twenty_two
end AspisR1.Port5Q1_Recurrence
end
