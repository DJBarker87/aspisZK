import R1Z.PV_Src_FrozenStages
import R1Z.PV_Src_Fixture_CanonicalFixtures

/-! Explicit transfer and withdrawal carriers in the smaller reference
instance. Both survive all unconditional primitive stages; compiler success
and installed public byte association remain separate obligations. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_FrozenFixtures
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_NativeInput PV_Src_FrozenInput
abbrev Scalar := PrivacyR1AcctBasis.K
local instance : CharP Scalar 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) Scalar).injective
    AspisCircleGroupOrder.P

def data (withdraw : Bool)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize)
    (pool domain destination : PV_Src_PublicRecords.Context) : Data (K := Scalar) where
  canonical := if withdraw then PV_Src_Fixture_CanonicalFixtures.withdrawal
    else PV_Src_Fixture_CanonicalFixtures.transfer
  index := 0x54321#u32
  indexBound := by cases withdraw <;> change 0 < 2^64 <;> decide
  compiled := compiled
  laneAnchor := anchor
  pool := pool
  domain := domain
  destination := destination

theorem both_primitive
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize)
    (pool domain destination : PV_Src_PublicRecords.Context) :
    ∀ withdraw : Bool, ∃ records banks,
      @newRecords PV_Src_FrozenInput.records
        (input (data withdraw compiled anchor pool domain destination)) = ok records ∧
      WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness records.w) ∧
      pair_forest_copy_builder.CopyRecords.banks records = ok (some banks) :=
  fun withdraw => PV_Src_FrozenStages.primitive _

theorem both_inhabited
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize)
    (pool domain destination : PV_Src_PublicRecords.Context) :
    ∃ transfer withdrawal : Data (K := Scalar),
      transfer.canonical = PV_Src_Fixture_CanonicalFixtures.transfer ∧
      withdrawal.canonical = PV_Src_Fixture_CanonicalFixtures.withdrawal ∧
      PV_Src_RecordReference.Checked (input transfer) ∧
      PV_Src_RecordReference.Checked (input withdrawal) := by
  refine ⟨data false compiled anchor pool domain destination,
    data true compiled anchor pool domain destination,rfl,rfl,?_,?_⟩
  · exact checked _
  · exact checked _

#print axioms both_primitive
#print axioms both_inhabited
end R1Z.PV_Src_FrozenFixtures
