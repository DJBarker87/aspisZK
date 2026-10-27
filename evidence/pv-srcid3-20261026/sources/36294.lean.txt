import R1Z.PV_Src_FrozenPublic
import R1Z.PV_Src_CheckedPipeline

/-! Every selected canonical carrier survives the discharged primitive stages.
The public stage retains exactly the original full-compiler success input. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_FrozenStages
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_NativeInput PV_Src_FrozenInput
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem primitive (i : Data (K := K)) :
    ∃ records banks,
      @newRecords PV_Src_FrozenInput.records (input i) = ok records ∧
      WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness records.w) ∧
      pair_forest_copy_builder.CopyRecords.banks records = ok (some banks) :=
  PV_Src_CheckedPipeline.stages PV_Src_CanonicalRoots.table (input i) (checked i)

theorem with_public (i : Data (K := K))
    (success : @run external PV_Src_FrozenInput.records (input i) = ok (.Ok (input i).compiled)) :
    ∃ records banks,
      @newRecords PV_Src_FrozenInput.records (input i) = ok records ∧
      WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness records.w) ∧
      pair_forest_copy_builder.CopyRecords.banks records = ok (some banks) ∧
      PubCorr (PV_Src_Forest_PrimitiveArguments.wordPublic records.p)
        (R1J.SpendWitnessMap.mapPub (K := K)
          (PV_Src_Public.canonicalPublic (publicInput (input i)))) := by
  obtain ⟨r,b,hr,hw,hb⟩ := primitive i
  exact ⟨r,b,hr,hw,hb,PV_Src_FrozenPublic.correspondence i success r hr⟩

#print axioms primitive
#print axioms with_public
end R1Z.PV_Src_FrozenStages
