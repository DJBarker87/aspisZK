import JFq_Queries
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_QueryValidation
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source : CheckpointBytes4Ops.validate JFq_Queries.value=ok (.Ok ()) := by
  simp only [CheckpointBytes4Ops.validate,CheckpointBytes4Ops.queryLoop,JFq_Queries.value,Array.make,
    List.mem_cons,List.mem_singleton,List.not_mem_nil,List.append_nil,List.cons_append]
  decide

#print axioms source
end AspisR1.JFq_QueryValidation
end
