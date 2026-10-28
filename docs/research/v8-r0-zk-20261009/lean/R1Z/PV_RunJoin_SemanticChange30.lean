import R1Z.PV_RunJoin_ChangeLift30
import R1Z.PV_RunJoin_CompilerReads30
import R1Z.PV_RunJoin_UniversalBuild22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticChange30
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap PV_Src_NativeInput
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def statement (i : Input) := mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput i))

def witness (i : Input) := BuilderCanonical.liftWitness (K := K)
  (BuilderRecordCanonical.witness (PV_Src_Forest_PrimitiveArguments.wordWitness
    (PV_RunJoin_UniversalBuild22.records i).w))

theorem change (i : Input) (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!) :
    (statement (K := K) i).change = AspisR1.SpendRelation.changeCommitment
      (statement (K := K) i) (witness (K := K) i) := by
  obtain ⟨r,hr,hchange⟩ := PV_RunJoin_CompilerReads30.change i.witness
    (outputValue i.request) (recipient i.request) i.change (forestPublic i.request)
    i.laneAnchor i.snapshot i.compiled success
  have hrecords : newRecords i = ok r := hr
  have hw := PV_RunJoin_UniversalRecords22.words i checked r hrecords
  have hp := PV_RunJoin_UniversalRecords22.publicCorr (K := K) i success frontier r hrecords
  have hpub : (statement (K := K) i).change = digK (forestPublic i.request).change_commitment := by
    cases hreq : i.request <;> funext j <;>
      simp only [statement,publicInput,hreq,PV_Src_Public.canonicalPublic,
        BuilderPublicProjection.transferPublic,BuilderPublicProjection.withdrawalPublic,
        mapPub,digK,liftU,map_natCast]
  have hc := PV_RunJoin_ChangeLift30.change_eq r (statement (K := K) i) hw hp _ hchange hpub
  rw [PV_RunJoin_UniversalRecords22.returned i r hrecords] at hc
  exact hc
#print axioms change
end R1Z.PV_RunJoin_SemanticChange30
