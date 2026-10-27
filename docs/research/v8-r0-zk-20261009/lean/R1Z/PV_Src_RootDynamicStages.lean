import R1Z.PV_Src_RecordRootDictionary
import R1Z.PV_Src_FrozenStages
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_RootDynamicStages
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_NativeInput PV_Src_FrozenInput
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem primitive (i : Data (K := K)) : ∃ r banks,
    @newRecords (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary) (input i) = ok r ∧
    WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness r.w) ∧
    pair_forest_copy_builder.CopyRecords.banks r = ok (some banks) := by
  rw [PV_Src_RecordRootDictionary.source]
  exact PV_Src_FrozenStages.primitive i

#print axioms primitive
end R1Z.PV_Src_RootDynamicStages
