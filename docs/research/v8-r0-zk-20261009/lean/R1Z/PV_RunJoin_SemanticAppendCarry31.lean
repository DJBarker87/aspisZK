import R1Z.PV_RunJoin_SemanticAppendRoot31
import R1Z.PV_RunJoin_RecordOutputLift31
import R1Z.PV_RunJoin_LateAppendCarry31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticAppendCarry31
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap PV_Src_NativeInput
open PV_RunJoin_SemanticChange30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem carry (i : Input) (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (small : R0P.digestCarry (statement (K := K) i).nextPairIndex < 20) :
    (statement (K := K) i).nextFrontier ⟨R0P.digestCarry (statement (K := K) i).nextPairIndex,small⟩ =
      AspisR1.AppendPath.pathPrefix (statement (K := K) i)
        (R0Z.BuilderModel.outPair (statement (K := K) i)
          (BuilderSpendRelation.modelWitness (witness (K := K) i)))
        (R0P.digestCarry (statement (K := K) i).nextPairIndex) := by
  obtain ⟨r,leaf,hr,hleaf,hlate⟩ := PV_RunJoin_CompilerAppend31.afterstate i.witness
    (outputValue i.request) (recipient i.request) i.change (forestPublic i.request)
    i.laneAnchor i.snapshot i.compiled success
  have hrecords : newRecords i = ok r := hr
  have hw := PV_RunJoin_UniversalRecords22.words i checked r hrecords
  have hp := PV_RunJoin_UniversalRecords22.publicCorr (K := K) i success frontier r hrecords
  have hleafMeaning := PV_RunJoin_RecordOutputLift31.output r (statement (K := K) i) hw hp leaf hleaf
  have hs := PV_RunJoin_UniversalRecords22.snapshot i success
  have hi : i.snapshot.next_pair_index.val = (statement (K := K) i).nextPairIndex := by
    cases hreq : i.request <;>
      simp only [statement,publicInput,PV_Src_NativeInput.transition,hreq,
        PV_Src_Public.canonicalPublic,BuilderPublicProjection.transferPublic,
        BuilderPublicProjection.withdrawalPublic,mapPub] <;> rw [hs]
  have hf : ∀ j : Fin 20, digK i.snapshot.frontier.val[j.val]! = (statement (K := K) i).snapshotFrontier j := by
    intro j
    cases hreq : i.request <;> funext lane <;>
      simp only [statement,publicInput,PV_Src_NativeInput.transition,hreq,
        PV_Src_Public.canonicalPublic,BuilderPublicProjection.transferPublic,
        BuilderPublicProjection.withdrawalPublic,mapPub] <;> rw [hs] <;>
      simp only [digK,liftU,map_natCast]
  have hmean := PV_RunJoin_LateAppendCarry31.carry (statement (K := K) i) _ r i.snapshot leaf _
    hi hleafMeaning.1 hleafMeaning.2 hf hlate small
  have hpub : (statement (K := K) i).nextFrontier ⟨R0P.digestCarry (statement (K := K) i).nextPairIndex,small⟩ =
      digK i.compiled.public_statement.candidate_afterstate.next_frontier.val[R0P.digestCarry (statement (K := K) i).nextPairIndex]! := by
    cases hreq : i.request <;> funext lane <;>
      simp only [statement,publicInput,PV_Src_NativeInput.transition,hreq,
        PV_Src_Public.canonicalPublic,BuilderPublicProjection.transferPublic,
        BuilderPublicProjection.withdrawalPublic,mapPub,digK,liftU,map_natCast]
  rw [PV_RunJoin_UniversalRecords22.returned i r hrecords] at hmean
  rw [hpub]
  unfold witness
  rw [BuilderFieldNormalization.decoded_witness]
  exact hmean
#print axioms carry
end R1Z.PV_RunJoin_SemanticAppendCarry31
