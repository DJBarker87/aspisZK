import NBG_Utilities
import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
noncomputable section
namespace NBG_Header
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind
abbrev E := pool_v1.payment_relation.PoolV1PaymentStatementFormatError

def tag : K → U8 | .PrivateTransfer => 1#u8 | .Withdrawal => 2#u8

theorem tag_result (kind : K) :
    UScalar.cast .U8 (read_discriminant kind : U8) = tag kind := by
  cases kind <;> rfl

theorem slice_equal (a b : Slice U8) (width : a.val.length = b.val.length) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 a b =
      ok (decide (a.val = b.val)) := by
  unfold core.slice.cmp.PartialEqSlice.eq
  rw [if_pos width]
  exact NBG_Utilities.lists a.val b.val width

def expected (bytes : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) : core.result.Result Unit E :=
  if bytes.val.take 4 ≠ magic.val then .Err .WrongMagic
  else if bytes.val[4]! ≠ 1#u8 then .Err .WrongVersion
  else if bytes.val[5]! ≠ tag kind then .Err .WrongTransitionKind
  else if bytes.val[6]! ≠ 1#u8 then .Err .WrongDigestEncoding
  else if bytes.val[7]! ≠ 0#u8 then .Err .NonZeroReserved
  else .Ok ()

theorem header_result (bytes : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) :
    pool_v1.payment_relation.require_header bytes magic kind = ok (expected bytes magic kind) := by
  simp [pool_v1.payment_relation.require_header,
    core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    Slice.len,Slice.length,Array.to_slice,bytes.property,magic.property,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    AspisR1TerminalDecoder.Slice.Insts.CoreCmpPartialEqSlice,slice_equal,
    Array.index_usize,tag_result,lift,bind_tc_ok,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,expected]
  repeat' split
  all_goals simp_all

#print axioms tag_result
#print axioms slice_equal
#print axioms header_result
end NBG_Header
