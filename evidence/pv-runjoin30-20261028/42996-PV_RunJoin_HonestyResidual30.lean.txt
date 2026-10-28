import R1Z.PV_RunJoin_SemanticResidual30
import R1Z.PV_RunJoin_CanonicalHonesty30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_HonestyResidual30
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap PV_Src_NativeInput
open PV_RunJoin_SemanticChange30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Each conjunct is still a proof obligation. This predicate is not a theorem
that canonical preparation establishes semantic admission. -/
def Remaining (i : Input) : Prop :=
  AspisR1.InputWitnessCore.Relation (statement (K := K) i)
    ((witness (K := K) i).inputValue.val : K) (witness (K := K) i).sk
    (witness (K := K) i).salt (witness (K := K) i).path (witness (K := K) i).pair ∧
  AspisR1.SpendRelation.variantOutput (statement (K := K) i) (witness (K := K) i) ∧
  AspisR1.SpendRelation.AppendBinding (statement (K := K) i) ∧
  ((statement (K := K) i).variant = .privateTransfer → (statement (K := K) i).change 7 ≠ 0)

theorem honest_iff (i : Input) (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (shape : AspisR1.PublicOptionShape.canonical (statement (K := K) i))
    (sum : (outputValue i.request).val+i.change.value.val=i.witness.pair.value.val) :
    PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) i ↔ Remaining (K := K) i := by
  have ha : PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) i ↔
      PV_RunJoin_UniversalBuild22.Admission (K := K) i :=
    ⟨fun h => h.1,fun h => ⟨h,success,checked,frontier⟩⟩
  exact ha.trans (PV_RunJoin_SemanticResidual30.admission_iff i shape
    (PV_RunJoin_SemanticValues30.balance i checked sum)
    (PV_RunJoin_SemanticChange30.change i success checked frontier))
#print axioms honest_iff
end R1Z.PV_RunJoin_HonestyResidual30
