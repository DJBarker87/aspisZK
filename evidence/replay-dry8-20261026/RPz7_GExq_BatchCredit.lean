import RPz7_GExq_CreditTactic
import RPz7_GExp_BatchStepBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_BatchCredit
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExq_Credit
open ControlFlow

def remaining : ControlFlow Port9OR_BatchStep.Next Port9OR_BatchStep.Out → Nat
  | .cont _ => 287
  | .done _ => 0

attribute [local irreducible] credit
attribute [local irreducible] Port9OR_BatchStep.verify Port4B_LeafCode.code

theorem body (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (root : Digest) (tree : Usize) (hash : Hash)
    (lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Port9OR_BatchStep.Indices) (val : Port9OR_BatchStep.Values) (d pos : Usize) :
    credit 288 remaining (Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos) := by
  unfold Port9OR_BatchStep.body
  repeat' first
    | (solve | apply pure_credit; simp only [remaining]; omega)
    | (solve | apply lift_credit; intro x; cases x <;> simp only [remaining] <;> omega)
    | (apply lift_bind_credit;intro x)
    | (credit_then_for 1 Port4B_LeafCode.code
        <;> first | omega | (solve | exact GExp_CountLaws.of_bounded _ _ (GExp_LeafBudget.leaf _ _)) | intro x)
    | (credit_then_for 288 Port9OR_BatchStep.verify
        <;> first | omega | (solve | apply GExp_BatchStepBudget.verify) | intro x)
    | split

#print axioms body
end AspisR1.GExq_BatchCredit
end
