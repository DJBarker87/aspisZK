import R1Z.PV_RunJoin_OuterABI30
import R1Z.PV_RunJoin_UniversalRecords22
set_option autoImplicit false
noncomputable section
namespace PV_RunJoin_Outer30
open Aeneas Aeneas.Std Result
open R1Z.PV_RunJoin_OuterABI30

def core.option.Option.Insts.CoreCmpPartialEqOption.ne {T : Type}
    (inst : Aeneas.Std.core.cmp.PartialEq T T) : Option T → Option T → Result Bool
  | none, none => ok false
  | some a, some b => inst.ne a b
  | _, _ => ok true

abbrev core.result.Result.map_err := @R1Z.BuilderAdmissionStd.mapErr

def aspis_core.field.P : Result U32 := ok 2147483647#u32
def pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY : Result U64 := ok 1048576#u64
def spend.VALUE_LIMIT : Result U32 := ok 1073741824#u32

/-- The remaining opaque source call is quantified, with no success law.
Theorems over this dictionary do not assert a native implementation. -/
class LaneRoot where
  call : pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1 →
    Result (Aeneas.Std.core.result.Result (Array U32 8#usize)
      pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1)

variable [lane : LaneRoot]
def pool_v1.pair_forest_trace.lane_root := lane.call

variable [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]

def pool_v1.pair_forest_trace.compile_forest_from_copies
    (input : pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option pool_v1.payment_relation.PoolV1OutputNoteWitnessV1)
    (change : pool_v1.payment_relation.PoolV1OutputNoteWitnessV1)
    (public1 : pool_v1.pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    Result (Aeneas.Std.core.result.Result
      pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
      pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) := do
  let r ← R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.compile_forest_from_copies
    (inputToForest input) out (recipient.map noteToForest) (noteToForest change)
    (publicToForest public1) anchor (snapshotToForest snapshot)
  ok (match r with
    | .Ok c => .Ok (compilationFromForest c)
    | .Err e => .Err (errorFromForest e))

def pool_v1.pair_trace.validate_common
    (pool domain : Array U8 32#usize) (seq : U64) (anchor nullifier : Array U32 8#usize)
    (asset : U32) (input : pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    Result (Aeneas.Std.core.result.Result Unit pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) := do
  let r ← AspisBuilderAdmissionSource.pool_v1.pair_trace.validate_common
    pool domain seq anchor nullifier asset (pairToAdmission input) (contextToAdmission context)
  ok (match r with
    | .Ok u => .Ok u
    | .Err e => .Err (errorFromAdmission e))

end PV_RunJoin_Outer30
