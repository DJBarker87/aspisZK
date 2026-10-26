import R1Z.PV_CurrentScale
import R1Z.ProverRwP7FibreArithmetic
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CurrentSquare
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev S := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.square

theorem complex (a : C) : S a = ProverRwP7FibreArithmetic.square a := by
  simp only [S,ProverRwP7CurrentFieldSource.aspis_core.field.CM31.square,
    ProverRwP7FibreArithmetic.square,ProverRwP7FibreSource.aspis_core.field.CM31.square,
    ProverRwP7FibreSource.aspis_core.field.P,
    ProverRwP7CurrentFieldSource.aspis_core.field.P,AspisR1ProducerRelease47.field.M31.reduce_u64,
    ProverRwP7CurrentBaseBridge.mreduce,ProverRwP7CurrentBaseBridge.mul,
    ProverRwP7CurrentBaseBridge.double,ProverRwSuccessCtReduce.reduce,
    ProverRwP7FibreSource.aspis_core.field.M31.mul,
    ProverRwP7FibreSource.aspis_core.field.M31.double,lift,bind_assoc_eq,bind_tc_ok]

 theorem total (a : C) : ∃ b, S a = ok b := by
  rw [complex]
  exact ProverRwP7FibreArithmetic.square_total a
#print axioms complex
#print axioms total
end R1Z.PV_CurrentSquare
