import R1Z.PV_RunJoin_RecipientLift31
import R1Z.PV_RunJoin_CompilerReads31
import R1Z.PV_RunJoin_SemanticChange30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticRecipient31
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap PV_Src_NativeInput
open PV_RunJoin_SemanticChange30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem recipient (i : Input) (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (hv : (statement (K := K) i).variant = .privateTransfer) :
    (statement (K := K) i).recipient = some (AspisR1.SpendRelation.recipientCommitment
      (statement (K := K) i) (witness (K := K) i)) := by
  cases hreq : i.request with
  | withdrawal p =>
    simp only [statement,publicInput,hreq,PV_Src_Public.canonicalPublic,
      BuilderPublicProjection.withdrawalPublic,mapPub] at hv
    cases hv
  | transfer p recipient =>
    obtain ⟨r,hr,hrec⟩ := PV_RunJoin_CompilerReads31.recipient i.witness
      (outputValue i.request) (PV_Src_NativeInput.recipient i.request) i.change (forestPublic i.request)
      i.laneAnchor i.snapshot i.compiled p.recipient_commitment (by simp only [hreq,forestPublic]) success
    have hrecords : newRecords i = ok r := hr
    have hw := PV_RunJoin_UniversalRecords22.words i checked r hrecords
    have hp := PV_RunJoin_UniversalRecords22.publicCorr (K := K) i success frontier r hrecords
    have hpub : (statement (K := K) i).recipient = some (digK p.recipient_commitment) := by
      simp only [statement,publicInput,hreq,PV_Src_Public.canonicalPublic,
        BuilderPublicProjection.transferPublic,mapPub,Option.map_some]
      congr 1
      funext j
      simp only [digK,liftU,map_natCast]
    have hmean := PV_RunJoin_RecipientLift31.recipient_eq r (statement (K := K) i) hw hp hv _ hrec hpub
    rw [PV_RunJoin_UniversalRecords22.returned i r hrecords] at hmean
    exact hmean
#print axioms recipient
end R1Z.PV_RunJoin_SemanticRecipient31
