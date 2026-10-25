import GExp_BatchLoopBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_BatchTreeBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_CountLaws

theorem tree (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Digest)
    (batch tree : Usize) (idx : Port9OR_BatchStep.Indices) (val : Port9OR_BatchStep.Values) :
    count 3744 (Port9OR_BatchTree.code base D hash proof queries root batch tree idx val) := by
  unfold Port9OR_BatchTree.code
  apply lift_bind_count; intro raw
  apply lift_bind_count; intro keys
  query_count_then_for 3744 Port9OR_BatchLoop.code
  · decide
  · intro H
    have bound := GExp_BatchLoopBudget.loop base D hash proof root tree
      (Port4B_TreeCuts.lo batch) (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch tree)
      keys ((Port4B_TreeCuts.count batch).val+1) idx val 0#usize 0#usize H
    apply bound.trans
    rw [(Port4B_Bounds.count batch).1]
    split <;> decide
  · intro out
    obtain ⟨idx,val,pending⟩ := out
    cases pending
    · exact lift_count _ _
    · exact pure_count _ _

#print axioms tree
end AspisR1.GExp_BatchTreeBudget
end
