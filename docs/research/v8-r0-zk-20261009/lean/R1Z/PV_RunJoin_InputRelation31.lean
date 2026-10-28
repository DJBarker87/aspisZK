import R1Z.PV_RunJoin_SemanticInput31
import R1Z.PV_RunJoin_PairValidation31
import R1Z.PV_RunJoin_PairValidationReads31
import R1Z.PV_RunJoin_PairSpendable31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InputRelation31
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_Src_NativeInput
open PV_RunJoin_SemanticChange30 PV_RunJoin_OuterABI30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def Relation (i : Input) : Prop := AspisR1.InputWitnessCore.Relation (statement (K := K) i)
  ((witness (K := K) i).inputValue.val : K) (witness (K := K) i).sk
  (witness (K := K) i).salt (witness (K := K) i).path (witness (K := K) i).pair

theorem pair_equal (i : Input) : (witness (K := K) i).pair =
    PV_RunJoin_PairValidation31.model (K := K) i.witness.pair.pair_leaf := by
  unfold PV_RunJoin_PairValidation31.model
  rw [← PV_RunJoin_WitnessViews31.pair_first i,← PV_RunJoin_WitnessViews31.pair_second i,
    ← PV_RunJoin_WitnessViews31.pair_occupied i,← PV_RunJoin_WitnessViews31.pair_inverse i]
#print axioms pair_equal

theorem valid (i : Input) (success : run i = ok (.Ok i.compiled)) :
    (witness (K := K) i).pair.Valid := by
  have hp := PV_RunJoin_PairValidationReads31.compiler_validated i.witness
    (outputValue i.request) (recipient i.request) i.change (forestPublic i.request)
    i.laneAnchor i.snapshot i.compiled success
  rw [pair_equal]
  exact PV_RunJoin_PairValidation31.valid _ hp
#print axioms valid

theorem relation (i : Input) (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (spend : (leafToAdmission (leafFromForest i.witness.pair.pair_leaf)).require_selected_spendable
      i.witness.pair.selected_second = ok (.Ok ())) : Relation (K := K) i := by
  exact ⟨valid i success,PV_RunJoin_PairSpendable31.semantic i spend,
    PV_RunJoin_SemanticInput31.commitment i success checked frontier,
    PV_RunJoin_SemanticInput31.sibling i,
    PV_RunJoin_SemanticInput31.nullifier i success checked frontier,
    PV_RunJoin_SemanticInput31.membership i success checked frontier⟩
#print axioms relation
end R1Z.PV_RunJoin_InputRelation31
