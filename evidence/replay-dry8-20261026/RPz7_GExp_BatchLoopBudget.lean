import RPz7_GExp_BatchStepBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_BatchLoopBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_CountLaws

theorem loop (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (fuel : Nat) (idx : Port9OR_BatchStep.Indices) (val : Port9OR_BatchStep.Values) (d pos : Usize) :
    count (288*fuel) (Port9OR_BatchLoop.code base D hash proof root tree lo n slot keys fuel idx val d pos) := by
  induction fuel generalizing idx val d pos with
  | zero => exact lift_count _ _
  | succ fuel ih =>
    unfold Port9OR_BatchLoop.code
    query_count_then_for 288 Port9OR_BatchStep.body
    · omega
    · exact GExp_BatchStepBudget.body _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · intro out
      cases out with
      | done result => exact pure_count _ _
      | cont next =>
        obtain ⟨ni,nv,nd,np⟩ := next
        have arithmetic : 288*(fuel+1)-288=288*fuel := by omega
        rw [arithmetic]
        exact ih ni nv nd np

#print axioms loop
end AspisR1.GExp_BatchLoopBudget
end
