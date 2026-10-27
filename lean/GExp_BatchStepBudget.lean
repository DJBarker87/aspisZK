import GExp_VerifyBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_BatchStepBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_CountLaws

theorem verify (root : Digest) (idx : Port9OR_BatchStep.Indices) (val : Port9OR_BatchStep.Values)
    (n : Usize) (nodes : Slice U8) : count 288 (Port9OR_BatchStep.verify root idx val n nodes) := by
  unfold Port9OR_BatchStep.verify
  query_count_then_for 288 Port9OR_P6Verify.code
  · decide
  · exact GExp_VerifyBudget.verify _ _ _
  · intro out
    exact pure_count _ _

attribute [local irreducible] Port9OR_BatchStep.verify Port4B_LeafCode.code

theorem body (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (root : Digest) (tree : Usize) (hash : Hash)
    (lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Port9OR_BatchStep.Indices) (val : Port9OR_BatchStep.Values) (d pos : Usize) :
    count 288 (Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos) := by
  unfold Port9OR_BatchStep.body
  repeat' first
    | (solve | apply pure_count)
    | (solve | apply lift_count)
    | (apply lift_bind_count;intro x)
    | (query_count_then_for 1 Port4B_LeafCode.code
       <;> first | omega | (solve | exact of_bounded _ _ (GExp_LeafBudget.leaf _ _)) | intro x)
    | (query_count_then_for 288 Port9OR_BatchStep.verify
       <;> first | omega | (solve | apply verify) | intro x)
    | split

#print axioms verify
#print axioms body
end AspisR1.GExp_BatchStepBudget
end
