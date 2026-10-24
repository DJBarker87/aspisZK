import OraclePortCheckpointResumeC5
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Recurrence
abbrev Model := OraclePortCheckpointStateC3.Prepared OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E
attribute [local irreducible] QueryAccumulator.run QueryAccumulator.run22

theorem ten (model : Model) :
    OraclePortCheckpointStateC3.advance model 10 QueryAccumulator.initial=
      (OraclePortCheckpointStateC3.write model).accumulator := by
  exact OraclePortCheckpointStateC3.advance_run model 10 0

theorem twenty_two (model : Model) :
    OraclePortCheckpointStateC3.advance model 12 (OraclePortCheckpointStateC3.write model).accumulator=
      QueryAccumulator.run22 model.iota model.rho model.values model.basis := by
  exact OraclePortCheckpointStateC3.advance_run model 12 10

#print axioms ten
#print axioms twenty_two
end AspisR1.Port5Q1_Recurrence
end
