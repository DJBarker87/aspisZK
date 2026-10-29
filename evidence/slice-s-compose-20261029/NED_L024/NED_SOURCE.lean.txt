import NBP_DigestDecode
import NBP_Read
import NBG_PaymentChecks
set_option autoImplicit false
noncomputable section
namespace NBP_CommonDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev E := pool_v1.payment_relation.PoolV1PaymentStatementFormatError

def asset (b : Array U8 216#usize) : U32 :=
  core.num.U32.from_le_bytes (NBP_Read.chunk (W:=4#usize) b 144 (by decide))

def common (b : Array U8 216#usize) (anchor nullifier : Array U32 8#usize) : C :=
  ⟨NBP_Read.chunk b 8 (by decide),NBP_Read.chunk b 40 (by decide),
    core.num.U64.from_le_bytes (NBP_Read.chunk b 72 (by decide)),anchor,nullifier,asset b⟩

def decoded (b : Array U8 216#usize) : core.result.Result C E :=
  if asset b >= 2147483647#u32 then .Err .NonCanonicalAssetId else
  match NBP_DigestDecode.decoded (NBP_Read.chunk b 80 (by decide)) with
  | .Err _ => .Err .NonCanonicalDigest
  | .Ok anchor =>
    match NBP_DigestDecode.decoded (NBP_Read.chunk b 112 (by decide)) with
    | .Err _ => .Err .NonCanonicalDigest
    | .Ok nullifier =>
      let c := common b anchor nullifier
      match NBG_PaymentChecks.common c with
      | .Err e => .Err e
      | .Ok () => .Ok c

theorem result (b : Array U8 216#usize) :
    pool_v1.payment_relation.decode_common b = ok (decoded b) := by
  simp [pool_v1.payment_relation.decode_common,
    pool_v1.payment_relation.ASSET_ID_OFFSET,pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,
    core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,Array.to_slice,Slice.length,Slice.len,b.property,
    core.array.TryFromArrayCopySlice.try_from,core.array.TryFromSharedArraySlice.try_from,
    atomic_statement.unwrap_fixed_slice,aspis_core.field.P,
    NBP_DigestDecode.result,NBG_PaymentChecks.common_result,
    asset,common,decoded,NBP_Read.chunk,lift,bind_tc_ok,List.slice,
    core.result.Result.map_err,
    pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,
    pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once,
    pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,
    pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
  repeat' split
  all_goals simp_all
#print axioms result
end NBP_CommonDecode
