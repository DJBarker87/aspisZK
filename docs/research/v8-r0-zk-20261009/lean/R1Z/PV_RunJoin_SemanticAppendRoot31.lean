import R1Z.PV_RunJoin_CompilerAppend31
import R1Z.PV_RunJoin_LateAppendRoot31
import R1Z.PV_RunJoin_RecordAppendLift31
import R1Z.PV_RunJoin_UniversalBuild22
import R1Z.PV_RunJoin_SemanticChange30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticAppendRoot31
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap PV_Src_NativeInput
open PV_RunJoin_SemanticChange30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem root (i : Input) (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!) :
    (statement (K := K) i).nextRoot = AspisR1.AppendPath.pathPrefix (statement (K := K) i)
      (R0Z.BuilderModel.outPair (statement (K := K) i) (BuilderSpendRelation.modelWitness (witness (K := K) i))) 20 := by
  obtain ⟨r,leaf,hr,hleaf,hlate⟩ := PV_RunJoin_CompilerAppend31.afterstate i.witness
    (outputValue i.request) (recipient i.request) i.change (forestPublic i.request)
    i.laneAnchor i.snapshot i.compiled success
  have hrecords : newRecords i = ok r := hr
  have hw := PV_RunJoin_UniversalRecords22.words i checked r hrecords
  have hp := PV_RunJoin_UniversalRecords22.publicCorr (K := K) i success frontier r hrecords
  have hread := PV_RunJoin_LateAppendRoot31.root r i.snapshot leaf _ hlate
  have hmean := PV_RunJoin_RecordAppendLift31.root r (statement (K := K) i) hw hp _ hread
  have hpub : (statement (K := K) i).nextRoot =
      digK i.compiled.public_statement.candidate_afterstate.next_root := by
    cases hreq : i.request <;> funext j <;>
      simp only [statement,publicInput,PV_Src_NativeInput.transition,hreq,
        PV_Src_Public.canonicalPublic,BuilderPublicProjection.transferPublic,
        BuilderPublicProjection.withdrawalPublic,mapPub,digK,liftU,map_natCast]
  rw [PV_RunJoin_UniversalRecords22.returned i r hrecords] at hmean
  rw [hpub]
  unfold witness
  rw [BuilderFieldNormalization.decoded_witness]
  exact hmean
#print axioms root
end R1Z.PV_RunJoin_SemanticAppendRoot31
