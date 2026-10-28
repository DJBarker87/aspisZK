import RPt_JFq_Queries
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_QueryValidation
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source : CheckpointBytes4Ops.validate JFq_Queries.value=ok (.Ok ()) := by
  norm_num [CheckpointBytes4Ops.validate,CheckpointBytes4Ops.queryLoop,JFq_Queries.value,
    Array.make,List.mem_append]

#print axioms source
end AspisR1.JFq_QueryValidation
end
