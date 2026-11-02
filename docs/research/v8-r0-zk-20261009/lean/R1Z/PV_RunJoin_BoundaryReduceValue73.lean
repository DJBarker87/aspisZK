import R1Z.ProverRwP6BoundaryReduce
import R1Z.PV_RunJoin_FieldData34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BoundaryReduceValue73
open Aeneas Aeneas.Std Result

theorem complete (x : U64) :
    ∃ z,ProverRwP6BoundarySource.aspis_core.field.M31.reduce_u64 x=ok z ∧
      z.val=x.val%AspisCircleGroupOrder.P ∧ z.val<AspisCircleGroupOrder.P := by
  obtain ⟨z,hz,hv,hc⟩ := AspisR1.ExtractedCurrentReducer.current_reduce_mod x
  have checked : AspisR1ProducerChecked47.field.reduce_u64 x=ok z := by
    rw [ProverCommitPrimitive47.reduce,hz]
  have release := ProverCommitRelease47.reduce x z checked
  exact ⟨z,(ProverRwSuccessCtReduce.reduce x).trans release,hv,hc⟩

#print axioms complete
end R1Z.PV_RunJoin_BoundaryReduceValue73
