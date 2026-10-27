import R1Z.PV_Src_RootDynamicStages
import R1Z.PV_Src_PublicRootClosed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_RootDynamicPublicStages
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_NativeInput PV_Src_FrozenInput
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem source (i : Data (K := K))
    (success : @run PV_Src_ExternalReference.dictionary
      (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary) (input i) =
        ok (.Ok (input i).compiled)) : ∃ r banks,
    @newRecords (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary) (input i) = ok r ∧
    WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness r.w) ∧
    pair_forest_copy_builder.CopyRecords.banks r = ok (some banks) ∧
    PubCorr (PV_Src_Forest_PrimitiveArguments.wordPublic r.p)
      (R1J.SpendWitnessMap.mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (input i)))) := by
  obtain ⟨r,b,hr,hw,hb⟩ := PV_Src_RootDynamicStages.primitive i
  exact ⟨r,b,hr,hw,hb,PV_Src_PublicRootClosed.correspondence (input i) success (frontier i) r hr⟩

#print axioms source
end R1Z.PV_Src_RootDynamicPublicStages
