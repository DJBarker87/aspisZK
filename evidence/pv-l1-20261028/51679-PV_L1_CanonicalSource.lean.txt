import PV_L1_Source_070
import R1Z.PV_RunJoin_CanonicalHonest31
import R1Z.PV_RunJoin_NativeSelectedInputs
set_option autoImplicit false
noncomputable section
namespace PV_L1_CanonicalSource
open Aeneas Aeneas.Std Result ProverRwFull
open R1Z R1Z.PV_RunJoin_Outer30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := PV_RunJoin_LaneABI31.native

/-- Complete emitted Result at the original nominal public/payload arguments.
This is not the V163 native body-data or V167 native-effect association. -/
def SourceResultLaw (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input) : Prop :=
  letI : ExternalTypes := PDict_CodecDictionary.native base
  letI : ExternalFuns := PDict_CodecDictionary.selected base ops
  ∀ attempt store,
    PV_L1_Logged.erase (PV_L1_Source_070.produce
      (PV_RunJoin_NominalPublicData.fromInput base i)
      (PV_RunJoin_NominalCompiledData.compiled base i.compiled)
      .S2 hash attempt store) =
    prover.prove_masked_attempt
      (PV_RunJoin_NominalPublicData.fromInput base i)
      (PV_RunJoin_NominalCompiledData.compiled base i.compiled)
      .S2 hash attempt store

theorem every_input (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input) : SourceResultLaw base ops hash i := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  letI : ExternalFuns := PDict_CodecDictionary.selected base ops
  intro attempt store
  exact PV_L1_Source_070.complete_result _ _ _ _ attempt store
#print axioms every_input

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem transfer (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (prepared : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      PV_RunJoin_ConsumerBoundary25.HonestInput (K := K)
        (PV_RunJoin_OuterChecked30.transferInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) ∧
      SourceResultLaw base ops hash
        (PV_RunJoin_OuterChecked30.transferInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) := by
  obtain ⟨root,hr,hi⟩ := PV_RunJoin_CanonicalHonest31.transfer (K := K) bytes p w context snapshot c prepared
  exact ⟨root,hr,hi,every_input base ops hash _⟩
#print axioms transfer

theorem withdrawal (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (prepared : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      PV_RunJoin_ConsumerBoundary25.HonestInput (K := K)
        (PV_RunJoin_OuterChecked30.withdrawalInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) ∧
      SourceResultLaw base ops hash
        (PV_RunJoin_OuterChecked30.withdrawalInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) := by
  obtain ⟨root,hr,hi⟩ := PV_RunJoin_CanonicalHonest31.withdrawal (K := K) bytes p w context snapshot c prepared
  exact ⟨root,hr,hi,every_input base ops hash _⟩
#print axioms withdrawal
end PV_L1_CanonicalSource
