import S6FullSourceCodecV1
import S6FiveCodecStdOptionsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6SourceCodec.Links

theorem link_0 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.Shared0T.Insts.CoreCloneClone = @AspisS6FiveUnrolledCodec.Shared0T.Insts.CoreCloneClone := by
  unfold AspisS6SourceCodec.Shared0T.Insts.CoreCloneClone AspisS6FiveUnrolledCodec.Shared0T.Insts.CoreCloneClone
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  <;> rfl

theorem link_1 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.Shared0T.Insts.CoreMarkerCopy = @AspisS6FiveUnrolledCodec.Shared0T.Insts.CoreMarkerCopy := by
  unfold AspisS6SourceCodec.Shared0T.Insts.CoreMarkerCopy AspisS6FiveUnrolledCodec.Shared0T.Insts.CoreMarkerCopy
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_0 unused]
  <;> rfl

theorem link_2 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.core.option.Option.Insts.CoreCmpPartialEqOption = @AspisS6FiveUnrolledCodec.core.option.Option.Insts.CoreCmpPartialEqOption (AspisS6FiveUnrolledCodec.StdOptions.ops unused) := by
  unfold AspisS6SourceCodec.core.option.Option.Insts.CoreCmpPartialEqOption AspisS6FiveUnrolledCodec.core.option.Option.Insts.CoreCmpPartialEqOption
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  <;> rfl

theorem link_3 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.core.result.Result.map_err = @AspisS6FiveUnrolledCodec.core.result.Result.map_err := by
  unfold AspisS6SourceCodec.core.result.Result.map_err AspisS6FiveUnrolledCodec.core.result.Result.map_err
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  <;> rfl

theorem link_4 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.Slice.Insts.CoreCmpPartialEqSlice = @AspisS6FiveUnrolledCodec.Slice.Insts.CoreCmpPartialEqSlice := by
  unfold AspisS6SourceCodec.Slice.Insts.CoreCmpPartialEqSlice AspisS6FiveUnrolledCodec.Slice.Insts.CoreCmpPartialEqSlice
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  <;> rfl

theorem link_5 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_core.field.P = @AspisS6FiveUnrolledCodec.aspis_core.field.P := by
  unfold AspisS6SourceCodec.aspis_core.field.P AspisS6FiveUnrolledCodec.aspis_core.field.P
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  <;> rfl

theorem link_6 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq = @AspisS6FiveUnrolledCodec.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq := by
  unfold AspisS6SourceCodec.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq AspisS6FiveUnrolledCodec.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  <;> rfl

theorem link_7 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 = @AspisS6FiveUnrolledCodec.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 := by
  unfold AspisS6SourceCodec.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 AspisS6FiveUnrolledCodec.aspis_core.field.M31.Insts.CoreCmpPartialEqM31
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_6 unused]
  <;> rfl

theorem link_8 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_core.field.M31.from_le_bytes = @AspisS6FiveUnrolledCodec.aspis_core.field.M31.from_le_bytes := by
  unfold AspisS6SourceCodec.aspis_core.field.M31.from_le_bytes AspisS6FiveUnrolledCodec.aspis_core.field.M31.from_le_bytes
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_5 unused]
  <;> rfl

theorem link_9 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_core.field.M31.to_le_bytes = @AspisS6FiveUnrolledCodec.aspis_core.field.M31.to_le_bytes := by
  unfold AspisS6SourceCodec.aspis_core.field.M31.to_le_bytes AspisS6FiveUnrolledCodec.aspis_core.field.M31.to_le_bytes
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  <;> rfl

theorem link_10 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical = @AspisS6FiveUnrolledCodec.aspis_statement.atomic_statement.encode_digest_canonical := by
  unfold AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical AspisS6FiveUnrolledCodec.aspis_statement.atomic_statement.encode_digest_canonical
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_9 unused]
  <;> rfl

theorem link_11 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.atomic_statement.unwrap_fixed_slice = @AspisS6FiveUnrolledCodec.aspis_statement.atomic_statement.unwrap_fixed_slice := by
  unfold AspisS6SourceCodec.aspis_statement.atomic_statement.unwrap_fixed_slice AspisS6FiveUnrolledCodec.aspis_statement.atomic_statement.unwrap_fixed_slice
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  <;> rfl

theorem link_12 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.atomic_statement.decode_digest_canonical = @AspisS6FiveUnrolledCodec.aspis_statement.atomic_statement.decode_digest_canonical (AspisS6FiveUnrolledCodec.StdOptions.ops unused) := by
  unfold AspisS6SourceCodec.aspis_statement.atomic_statement.decode_digest_canonical AspisS6FiveUnrolledCodec.aspis_statement.atomic_statement.decode_digest_canonical
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_8 unused]
  <;> rfl

theorem link_13 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  <;> rfl

theorem link_14 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  <;> rfl

theorem link_15 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_14 unused]
  <;> rfl

theorem link_16 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  <;> rfl

theorem link_17 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_5 unused]
  <;> rfl

theorem link_18 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_17 unused]
  <;> rfl

theorem link_19 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical
  simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_18 unused]
  <;> rfl

end AspisS6SourceCodec.Links
