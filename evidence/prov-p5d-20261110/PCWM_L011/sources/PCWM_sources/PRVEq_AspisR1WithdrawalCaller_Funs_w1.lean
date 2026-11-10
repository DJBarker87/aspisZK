-- PCWM_ w1: fresh frozen-4bb3b3f (overflow checks ON) definitions of the five WithdrawalCaller.Funs items that are not loops, against the gate constants.
-- fresh sources: spend.VALUE_LIMIT <- PCQF_E003; POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_TREE_DEPTH <- PCQF_E010; POOL_V1_LEAF_CAPACITY <- PCQF_E004; M31.to_le_bytes <- PCWM_E001. Text is verbatim.
import Aeneas
import AspisR1WithdrawalCaller.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
namespace AspisR1WithdrawalCaller
namespace PRVFresh_AspisR1WithdrawalCaller_Funs_w1
/-- fresh type aspis_core::field::M31 (frozen Types text: `def field.M31 := Std.U32`) -/
@[reducible] def field.M31 := Std.U32
/-- [aspis_statement::spend::VALUE_LIMIT]
    Source: 'crates/aspis-statement/src/spend.rs', lines 9:0-9:37
    Visibility: public -/
@[global_simps, irreducible]
def spend.VALUE_LIMIT : Result Std.U32 := 1#u32 <<< 30#i32

/-- [aspis_statement::pool_v1::format::POOL_V1_DIGEST_ENCODING_VERSION]
    Source: 'crates/aspis-statement/src/pool_v1/format.rs', lines 27:0-27:50
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION : Std.U8 := 1#u8

/-- [aspis_statement::pool_v1::format::POOL_V1_TREE_DEPTH]
    Source: 'crates/aspis-statement/src/pool_v1/format.rs', lines 28:0-28:41
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.format.POOL_V1_TREE_DEPTH : Std.Usize := 20#usize

/-- [aspis_statement::pool_v1::incremental_merkle::POOL_V1_LEAF_CAPACITY]
    Source: 'crates/aspis-statement/src/pool_v1/incremental_merkle.rs', lines 26:0-26:66
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY : Result Std.U64 :=
  1#u64 <<< pool_v1.format.POOL_V1_TREE_DEPTH

/-- [aspis_core::field::{aspis_core::field::M31}::to_le_bytes]:
    Source: 'crates/aspis-core/src/field.rs', lines 248:4-250:5
    Visibility: public -/
def field.M31.to_le_bytes
  (self : field.M31) : Result (Array Std.U8 4#usize) := do
  ok (core.num.U32.to_le_bytes self)

/-- PCWM_ cross-crate binding: in the aspis-statement emission (PCWM_E002) the aspis-core method `M31::to_le_bytes` is an external; it is instantiated to the frozen aspis-core emission PCWM_E001 above (CONDITIONAL_ON_BINDING). -/
def aspis_core.field.M31.to_le_bytes (self : aspis_core.field.M31) : Result (Array Std.U8 4#usize) := field.M31.to_le_bytes self

/-- [aspis_statement::atomic_statement::encode_digest_canonical]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_statement.rs', lines 75:4-77:5
    Visibility: public -/
def atomic_statement.encode_digest_canonical_loop.body
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  aspis_core.field.M31)) (bytes : Array Std.U8 32#usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter aspis_core.field.M31)) × (Array Std.U8 32#usize))
    (Array Std.U8 32#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.M31) iter
  match o with
  | none => ok (done bytes)
  | some p =>
    let (index, value) := p
    let i ← index * 4#usize
    let i1 ← i + 4#usize
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes
        { start := i, «end» := i1 }
    let a ← aspis_core.field.M31.to_le_bytes value
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let bytes1 := index_mut_back s2
    ok (cont (iter1, bytes1))

/-- [aspis_statement::atomic_statement::encode_digest_canonical]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_statement.rs', lines 75:4-77:5
    Visibility: public -/
def atomic_statement.encode_digest_canonical_loop.body
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  aspis_core.field.M31)) (bytes : Array Std.U8 32#usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter aspis_core.field.M31)) × (Array Std.U8 32#usize))
    (Array Std.U8 32#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.M31) iter
  match o with
  | none => ok (done bytes)
  | some p =>
    let (index, value) := p
    let i ← index * 4#usize
    let i1 ← i + 4#usize
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes
        { start := i, «end» := i1 }
    let a ← aspis_core.field.M31.to_le_bytes value
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let bytes1 := index_mut_back s2
    ok (cont (iter1, bytes1))

/-- [aspis_statement::atomic_statement::encode_digest_canonical]:
    Source: 'crates/aspis-statement/src/atomic_statement.rs', lines 73:0-79:1
    Visibility: public -/
def atomic_statement.encode_digest_canonical
  (digest : Array aspis_core.field.M31 8#usize) :
  Result (Array Std.U8 32#usize)
  := do
  let bytes := Array.repeat 32#usize 0#u8
  let s ← lift (Array.to_slice digest)
  let i ← core.slice.Slice.iter s
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.M31) i
  atomic_statement.encode_digest_canonical_loop iter bytes


end PRVFresh_AspisR1WithdrawalCaller_Funs_w1
end AspisR1WithdrawalCaller

namespace PRVEq.AspisR1WithdrawalCaller.Funs_w1
open AspisR1WithdrawalCaller

theorem pool_v1.POOL_V1_TREE_DEPTH : AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.format.POOL_V1_TREE_DEPTH = AspisR1WithdrawalCaller.pool_v1.POOL_V1_TREE_DEPTH := by
  unfold AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.format.POOL_V1_TREE_DEPTH AspisR1WithdrawalCaller.pool_v1.POOL_V1_TREE_DEPTH; rfl
#print axioms pool_v1.POOL_V1_TREE_DEPTH

theorem pool_v1.POOL_V1_DIGEST_ENCODING_VERSION : AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION = AspisR1WithdrawalCaller.pool_v1.POOL_V1_DIGEST_ENCODING_VERSION := by
  unfold AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION AspisR1WithdrawalCaller.pool_v1.POOL_V1_DIGEST_ENCODING_VERSION; rfl
#print axioms pool_v1.POOL_V1_DIGEST_ENCODING_VERSION

theorem VALUE_LIMIT : AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.spend.VALUE_LIMIT = AspisR1WithdrawalCaller.VALUE_LIMIT := by
  unfold AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.spend.VALUE_LIMIT AspisR1WithdrawalCaller.VALUE_LIMIT; rfl
#print axioms VALUE_LIMIT

/-- the fresh capacity is `1 <<< fresh TREE_DEPTH`, the gate's is `1 <<< gate TREE_DEPTH`; equal by the depth equality -/
theorem pool_v1.POOL_V1_LEAF_CAPACITY : AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY = AspisR1WithdrawalCaller.pool_v1.POOL_V1_LEAF_CAPACITY := by
  unfold AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY AspisR1WithdrawalCaller.pool_v1.POOL_V1_LEAF_CAPACITY
  rw [pool_v1.POOL_V1_TREE_DEPTH]
#print axioms pool_v1.POOL_V1_LEAF_CAPACITY

theorem aspis_core.field.M31.to_le_bytes : @AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.field.M31.to_le_bytes = @AspisR1WithdrawalCaller.aspis_core.field.M31.to_le_bytes := by
  rfl
#print axioms aspis_core.field.M31.to_le_bytes


theorem encode_digest_canonical_loop.body : @AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.atomic_statement.encode_digest_canonical_loop.body = @AspisR1WithdrawalCaller.encode_digest_canonical_loop.body := by
  rfl
#print axioms encode_digest_canonical_loop.body

theorem encode_digest_canonical_loop : @AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.atomic_statement.encode_digest_canonical_loop = @AspisR1WithdrawalCaller.encode_digest_canonical_loop := by
  rfl
#print axioms encode_digest_canonical_loop

theorem encode_digest_canonical : @AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.atomic_statement.encode_digest_canonical = @AspisR1WithdrawalCaller.encode_digest_canonical := by
  rfl
#print axioms encode_digest_canonical

end PRVEq.AspisR1WithdrawalCaller.Funs_w1
