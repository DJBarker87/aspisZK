import R1Z.PV_RunJoin_SemanticOptions30
import R1Z.PV_RunJoin_SemanticValues30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticResidual30
open R0Z.WriterRefine R1J.SpendWitnessMap PV_Src_NativeInput
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
open PV_RunJoin_SemanticChange30

/-- The remaining obligations are individual semantic relations, not Admission
or a successful call hidden in another predicate. -/
theorem admission_iff (i : Input)
    (shape : AspisR1.PublicOptionShape.canonical (statement (K := K) i))
    (balance : (witness (K := K) i).inputValue.val =
      (witness (K := K) i).outputValue.val+(witness (K := K) i).changeValue.val)
    (change : (statement (K := K) i).change = AspisR1.SpendRelation.changeCommitment
      (statement (K := K) i) (witness (K := K) i)) :
    PV_RunJoin_UniversalBuild22.Admission (K := K) i ↔
      AspisR1.InputWitnessCore.Relation (statement (K := K) i)
        ((witness (K := K) i).inputValue.val : K) (witness (K := K) i).sk
        (witness (K := K) i).salt (witness (K := K) i).path (witness (K := K) i).pair ∧
      AspisR1.SpendRelation.variantOutput (statement (K := K) i) (witness (K := K) i) ∧
      AspisR1.SpendRelation.AppendBinding (statement (K := K) i) ∧
      ((statement (K := K) i).variant = .privateTransfer →
        (statement (K := K) i).change 7 ≠ 0) := by
  change (AspisR1.SpendRelation.Rspend (statement (K := K) i) (witness (K := K) i) ∧ _) ↔ _
  unfold AspisR1.SpendRelation.Rspend
  simp only [shape,balance,change,true_and]
  tauto
#print axioms admission_iff
end R1Z.PV_RunJoin_SemanticResidual30
