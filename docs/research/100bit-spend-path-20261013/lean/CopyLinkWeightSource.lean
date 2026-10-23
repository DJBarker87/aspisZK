import Aeneas
import ImportUnionNamedDiscriminant
import CopyEndpointSource
import CopyLinkBitArithmetic

/-! Exact link-weight source and source descriptor. Endpoint carrier is the
same prior exact source owner; inverse type-name map is retained. -/
set_option autoImplicit false
namespace AspisR1CopyLinkWeightCandidate
open Aeneas Aeneas.Std Result Error
open AspisR1SelectedMaskProbe

@[import_union_discriminant isize]
inductive pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1
  where
| PrivateTransfer :
  pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1
| Withdrawal :
  pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1

structure pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestLink where
  tag : Std.U32
  weight_kind : Std.U8
  weight_level : Std.U8
  producer : AspisR1CopyEndpointCandidate.pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestEndpoint
  consumer : AspisR1CopyEndpointCandidate.pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestEndpoint

def
  pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq
  (self : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
  (other : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
  :
  Result Bool
  := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

@[global_simps, irreducible] def field.M31.ONE : field.M31 := 1#u32

def pool_v1.pair_forest_copy_terminal.link_weight
  (link : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestLink)
  (append_index : Std.U64)
  (variant :
  pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1) :
  Result field.M31
  := do
  match link.weight_kind with
  | 0#uscalar => ok field.M31.ONE
  | 1#uscalar =>
    let b ←
      pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq
        variant
        pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.PrivateTransfer
    let i ← lift (core.convert.num.FromU32Bool.from b)
    ok i
  | 2#uscalar =>
    let b ←
      pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq
        variant
        pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Withdrawal
    let i ← lift (core.convert.num.FromU32Bool.from b)
    ok i
  | 3#uscalar =>
    let i ← append_index >>> link.weight_level
    let i1 ← lift (i &&& 1#u64)
    let i2 ← lift (UScalar.cast .U32 i1)
    let i3 ← 1#u32 - i2
    ok i3
  | 4#uscalar =>
    let i ← append_index >>> link.weight_level
    let i1 ← lift (i &&& 1#u64)
    let i2 ← lift (UScalar.cast .U32 i1)
    ok i2
  | _ => fail panic

end AspisR1CopyLinkWeightCandidate
