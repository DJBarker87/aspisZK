import R1Z.PV_RunJoin_HonestyResidual30
import R1Z.PV_RunJoin_AppendBinding31
import R1Z.PV_RunJoin_SemanticSentinel31
import R1Z.PV_RunJoin_InputRelation31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_HonestPackage31
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_Src_NativeInput
open PV_RunJoin_SemanticChange30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem honest (i : Input) (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (shape : AspisR1.PublicOptionShape.canonical (statement (K := K) i))
    (sum : (outputValue i.request).val+i.change.value.val=i.witness.pair.value.val)
    (input : PV_RunJoin_InputRelation31.Relation (K := K) i)
    (variant : AspisR1.SpendRelation.variantOutput (statement (K := K) i) (witness (K := K) i)) :
    PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) i := by
  apply (PV_RunJoin_HonestyResidual30.honest_iff i success checked frontier shape sum).mpr
  exact ⟨input,variant,PV_RunJoin_AppendBinding31.append i success checked frontier variant,
    PV_RunJoin_SemanticSentinel31.sentinel i success⟩
#print axioms honest
end R1Z.PV_RunJoin_HonestPackage31
