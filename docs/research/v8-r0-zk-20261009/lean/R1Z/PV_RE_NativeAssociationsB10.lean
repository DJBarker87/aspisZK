import R1Z.PV_Src_ExternalAssociation
import R1Z.PV_Src_RecordAssociation
import R1Z.PV_Src_FrozenFixtures
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NativeAssociationsB10
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
local instance : CharP PV_Src_FrozenFixtures.Scalar 2147483647 :=
  charP_of_injective_algebraMap
    (algebraMap (ZMod AspisCircleGroupOrder.P) PV_Src_FrozenFixtures.Scalar).injective
    AspisCircleGroupOrder.P

/-- Joint non-vacuity of the two exact association predicates on their
reference dictionaries. This does not install either reference natively. -/
theorem joint :
    PV_Src_ExternalAssociation.Associated PV_Src_FrozenInput.external ∧
    PV_Src_RecordAssociation.Associated PV_Src_FrozenInput.external PV_Src_FrozenInput.records := by
  constructor
  · intro s
    rfl
  · intro input out rec chg snapshot asset
    exact (PV_Src_RecordRootClosed.call input out rec chg snapshot asset).symm

/-- Both actual fixture constructors have returned records and banks in the
dynamic reference dictionary satisfying the exact associations above.
Compiled payload and public context parameters remain explicit. -/
theorem both_records
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize)
    (pool domain destination : PV_Src_PublicRecords.Context) :
    ∀ withdraw : Bool, ∃ records banks,
      @newRecords (@PV_Src_RecordDynamic.dictionary PV_Src_FrozenInput.external)
        (PV_Src_FrozenInput.input (PV_Src_FrozenFixtures.data withdraw compiled anchor pool domain destination)) = ok records ∧
      R0Z.WriterRefine.WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness records.w) ∧
      pair_forest_copy_builder.CopyRecords.banks records = ok (some banks) := by
  have same := PV_Src_RecordAssociation.dictionary PV_Src_FrozenInput.external
    PV_Src_FrozenInput.records joint.2
  rw [← same]
  exact PV_Src_FrozenFixtures.both_primitive compiled anchor pool domain destination
#print axioms joint
#print axioms both_records
end R1Z.PV_RE_NativeAssociationsB10
