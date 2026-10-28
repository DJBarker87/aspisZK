import R1Z.PV_RunJoin_SemanticAppendCarry31
import R1Z.PV_RunJoin_OutputPairMeaning31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AppendBinding31
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_Src_NativeInput
open PV_RunJoin_SemanticChange30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- The variant output clause is explicit here until the outer-route recipient
and withdrawal obligations are composed. -/
theorem append (i : Input) (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (variant : AspisR1.SpendRelation.variantOutput (statement (K := K) i) (witness (K := K) i)) :
    AspisR1.SpendRelation.AppendBinding (statement (K := K) i) := by
  refine ⟨R0Z.BuilderModel.outPair (statement (K := K) i)
    (BuilderSpendRelation.modelWitness (witness (K := K) i)),?_,?_,?_⟩
  · exact PV_RunJoin_OutputPairMeaning31.output _ _ (change i success checked frontier) variant
  · exact PV_RunJoin_SemanticAppendRoot31.root i success checked frontier
  · intro small
    exact PV_RunJoin_SemanticAppendCarry31.carry i success checked frontier small
#print axioms append
end R1Z.PV_RunJoin_AppendBinding31
