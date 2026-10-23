import S6FullSourceCodecV1
import S6SourceAgreementPart03V1
import S6SourceAgreementContextV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6SourceCodec.Links
open AspisS6FiveUnrolledCodec

theorem link_80 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_74 unused]
  all_goals rfl

#print axioms link_80

theorem link_81 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  all_goals rfl

#print axioms link_81

theorem link_82 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_74 unused, link_79 unused, link_80 unused, link_81 unused]
  all_goals rfl

#print axioms link_82

private def context_83 (dep_10 : codec_type% @AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical) (dep_26 : codec_type% @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES) (dep_76 : codec_type% @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1) (dep_77 : codec_type% @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION) (dep_78 : codec_type% @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC) (dep_82 : codec_type% @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING) (snapshot : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) (output : Slice Std.U8) : Result ((core.result.Result Unit aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) × (Slice Std.U8)) := do
  let i := Slice.len output
  if i != dep_26
  then ok (core.result.Result.Err aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongLength, output)
  else
    let r ← dep_76 snapshot
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let output1 ← core.slice.Slice.fill core.clone.CloneU8 output 0#u8
      let (s, index_mut_back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) output1 { «end» := 8#usize }
      let s1 ← lift (Array.to_slice dep_78)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let output2 := index_mut_back s2
      let output3 ← Slice.update output2 8#usize dep_77
      let (s3, index_mut_back1) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output3 { start := 16#usize, «end» := 48#usize }
      let a ← dep_82
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
      let output4 := index_mut_back1 s5
      let (s6, index_mut_back2) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output4 { start := 48#usize, «end» := 80#usize }
      let s7 ← lift (Array.to_slice snapshot.pool)
      let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
      let output5 := index_mut_back2 s8
      let (s9, index_mut_back3) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output5 { start := 80#usize, «end» := 112#usize }
      let s10 ← lift (Array.to_slice snapshot.deployment_domain)
      let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
      let output6 := index_mut_back3 s11
      let (s12, index_mut_back4) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output6 { start := 112#usize, «end» := 120#usize }
      let a1 ← lift (core.num.U64.to_le_bytes snapshot.sequence)
      let s13 ← lift (Array.to_slice a1)
      let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
      let output7 := index_mut_back4 s14
      let (s15, index_mut_back5) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output7 { start := 120#usize, «end» := 128#usize }
      let a2 ← lift (core.num.U64.to_le_bytes snapshot.next_pair_index)
      let s16 ← lift (Array.to_slice a2)
      let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
      let output8 := index_mut_back5 s17
      let (s18, index_mut_back6) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output8 { start := 128#usize, «end» := 160#usize }
      let a3 ← dep_10 snapshot.current_root
      let s19 ← lift (Array.to_slice a3)
      let s20 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s18 s19
      let output9 := index_mut_back6 s20
      let (s21, index_mut_back7) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output9 { start := 160#usize, «end» := 192#usize }
      let a4 ← Array.index_usize snapshot.frontier 0#usize
      let a5 ← dep_10 a4
      let s22 ← lift (Array.to_slice a5)
      let s23 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s21 s22
      let output10 := index_mut_back7 s23
      let (s24, index_mut_back8) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output10 { start := 192#usize, «end» := 224#usize }
      let a6 ← Array.index_usize snapshot.frontier 1#usize
      let a7 ← dep_10 a6
      let s25 ← lift (Array.to_slice a7)
      let s26 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s24 s25
      let output11 := index_mut_back8 s26
      let (s27, index_mut_back9) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output11 { start := 224#usize, «end» := 256#usize }
      let a8 ← Array.index_usize snapshot.frontier 2#usize
      let a9 ← dep_10 a8
      let s28 ← lift (Array.to_slice a9)
      let s29 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s27 s28
      let output12 := index_mut_back9 s29
      let (s30, index_mut_back10) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output12 { start := 256#usize, «end» := 288#usize }
      let a10 ← Array.index_usize snapshot.frontier 3#usize
      let a11 ← dep_10 a10
      let s31 ← lift (Array.to_slice a11)
      let s32 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s30 s31
      let output13 := index_mut_back10 s32
      let (s33, index_mut_back11) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output13 { start := 288#usize, «end» := 320#usize }
      let a12 ← Array.index_usize snapshot.frontier 4#usize
      let a13 ← dep_10 a12
      let s34 ← lift (Array.to_slice a13)
      let s35 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s33 s34
      let output14 := index_mut_back11 s35
      let (s36, index_mut_back12) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output14 { start := 320#usize, «end» := 352#usize }
      let a14 ← Array.index_usize snapshot.frontier 5#usize
      let a15 ← dep_10 a14
      let s37 ← lift (Array.to_slice a15)
      let s38 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s36 s37
      let output15 := index_mut_back12 s38
      let (s39, index_mut_back13) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output15 { start := 352#usize, «end» := 384#usize }
      let a16 ← Array.index_usize snapshot.frontier 6#usize
      let a17 ← dep_10 a16
      let s40 ← lift (Array.to_slice a17)
      let s41 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s39 s40
      let output16 := index_mut_back13 s41
      let (s42, index_mut_back14) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output16 { start := 384#usize, «end» := 416#usize }
      let a18 ← Array.index_usize snapshot.frontier 7#usize
      let a19 ← dep_10 a18
      let s43 ← lift (Array.to_slice a19)
      let s44 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s42 s43
      let output17 := index_mut_back14 s44
      let (s45, index_mut_back15) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output17 { start := 416#usize, «end» := 448#usize }
      let a20 ← Array.index_usize snapshot.frontier 8#usize
      let a21 ← dep_10 a20
      let s46 ← lift (Array.to_slice a21)
      let s47 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s45 s46
      let output18 := index_mut_back15 s47
      let (s48, index_mut_back16) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output18 { start := 448#usize, «end» := 480#usize }
      let a22 ← Array.index_usize snapshot.frontier 9#usize
      let a23 ← dep_10 a22
      let s49 ← lift (Array.to_slice a23)
      let s50 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s48 s49
      let output19 := index_mut_back16 s50
      let (s51, index_mut_back17) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output19 { start := 480#usize, «end» := 512#usize }
      let a24 ← Array.index_usize snapshot.frontier 10#usize
      let a25 ← dep_10 a24
      let s52 ← lift (Array.to_slice a25)
      let s53 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s51 s52
      let output20 := index_mut_back17 s53
      let (s54, index_mut_back18) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output20 { start := 512#usize, «end» := 544#usize }
      let a26 ← Array.index_usize snapshot.frontier 11#usize
      let a27 ← dep_10 a26
      let s55 ← lift (Array.to_slice a27)
      let s56 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s54 s55
      let output21 := index_mut_back18 s56
      let (s57, index_mut_back19) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output21 { start := 544#usize, «end» := 576#usize }
      let a28 ← Array.index_usize snapshot.frontier 12#usize
      let a29 ← dep_10 a28
      let s58 ← lift (Array.to_slice a29)
      let s59 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s57 s58
      let output22 := index_mut_back19 s59
      let (s60, index_mut_back20) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output22 { start := 576#usize, «end» := 608#usize }
      let a30 ← Array.index_usize snapshot.frontier 13#usize
      let a31 ← dep_10 a30
      let s61 ← lift (Array.to_slice a31)
      let s62 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s60 s61
      let output23 := index_mut_back20 s62
      let (s63, index_mut_back21) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output23 { start := 608#usize, «end» := 640#usize }
      let a32 ← Array.index_usize snapshot.frontier 14#usize
      let a33 ← dep_10 a32
      let s64 ← lift (Array.to_slice a33)
      let s65 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s63 s64
      let output24 := index_mut_back21 s65
      let (s66, index_mut_back22) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output24 { start := 640#usize, «end» := 672#usize }
      let a34 ← Array.index_usize snapshot.frontier 15#usize
      let a35 ← dep_10 a34
      let s67 ← lift (Array.to_slice a35)
      let s68 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s66 s67
      let output25 := index_mut_back22 s68
      let (s69, index_mut_back23) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output25 { start := 672#usize, «end» := 704#usize }
      let a36 ← Array.index_usize snapshot.frontier 16#usize
      let a37 ← dep_10 a36
      let s70 ← lift (Array.to_slice a37)
      let s71 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s69 s70
      let output26 := index_mut_back23 s71
      let (s72, index_mut_back24) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output26 { start := 704#usize, «end» := 736#usize }
      let a38 ← Array.index_usize snapshot.frontier 17#usize
      let a39 ← dep_10 a38
      let s73 ← lift (Array.to_slice a39)
      let s74 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s72 s73
      let output27 := index_mut_back24 s74
      let (s75, index_mut_back25) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output27 { start := 736#usize, «end» := 768#usize }
      let a40 ← Array.index_usize snapshot.frontier 18#usize
      let a41 ← dep_10 a40
      let s76 ← lift (Array.to_slice a41)
      let s77 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s75 s76
      let output28 := index_mut_back25 s77
      let (s78, index_mut_back26) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output28 { start := 768#usize, «end» := 800#usize }
      let a42 ← Array.index_usize snapshot.frontier 19#usize
      let a43 ← dep_10 a42
      let s79 ← lift (Array.to_slice a43)
      let s80 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s78 s79
      let output29 := index_mut_back26 s80
      ok (core.result.Result.Ok (), output29)
    | core.ops.control_flow.ControlFlow.Break residual => let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
                                                          ok (r1, output)




theorem link_83 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 := by
  have h : @context_83 (@AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical) (@AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES) (@AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1) (@AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION) (@AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC) (@AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING) = @context_83 (@AspisS6FiveUnrolledCodec.aspis_statement.atomic_statement.encode_digest_canonical) (@AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES) (@AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1) (@AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION) (@AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC) (@AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING) := by
    rw [link_10 unused, link_26 unused, link_76 unused, link_77 unused, link_78 unused, link_82 unused]
  exact h

#print axioms link_83

theorem link_84 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  all_goals rfl

#print axioms link_84

theorem link_85 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  all_goals rfl

#print axioms link_85

theorem link_86 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  all_goals rfl

#print axioms link_86

theorem link_87 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_73 unused, link_75 unused]
  all_goals rfl

#print axioms link_87

theorem link_88 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  all_goals rfl

#print axioms link_88

theorem link_89 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  all_goals rfl

#print axioms link_89

private def context_90 (dep_10 : codec_type% @AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical) (dep_13 : codec_type% @AspisS6SourceCodec.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION) (dep_81 : codec_type% @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION) (dep_87 : codec_type% @AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate) (dep_88 : codec_type% @AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC) (dep_89 : codec_type% @AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION) (afterstate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : Result (core.result.Result (Array Std.U8 688#usize) aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let r ← dep_87 afterstate
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let output := Array.repeat 688#usize 0#u8
    let (s, index_mut_back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output { «end» := 4#usize }
    let s1 ← lift (Array.to_slice dep_88)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let output1 := index_mut_back s2
    let output2 ← Array.update output1 4#usize dep_89
    let output3 ← Array.update output2 5#usize dep_81
    let output4 ← Array.update output3 6#usize dep_13
    let output5 ← Array.update output4 7#usize 1#u8
    let (s3, index_mut_back1) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5 { start := 8#usize, «end» := 16#usize }
    let a ← lift (core.num.U64.to_le_bytes afterstate.next_pair_index)
    let s4 ← lift (Array.to_slice a)
    let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
    let output6 := index_mut_back1 s5
    let (s6, index_mut_back2) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output6 { start := 16#usize, «end» := 48#usize }
    let a1 ← dep_10 afterstate.next_root
    let s7 ← lift (Array.to_slice a1)
    let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
    let output7 := index_mut_back2 s8
    let (s9, index_mut_back3) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output7 { start := 48#usize, «end» := 80#usize }
    let a2 ← Array.index_usize afterstate.next_frontier 0#usize
    let a3 ← dep_10 a2
    let s10 ← lift (Array.to_slice a3)
    let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
    let output8 := index_mut_back3 s11
    let (s12, index_mut_back4) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output8 { start := 80#usize, «end» := 112#usize }
    let a4 ← Array.index_usize afterstate.next_frontier 1#usize
    let a5 ← dep_10 a4
    let s13 ← lift (Array.to_slice a5)
    let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
    let output9 := index_mut_back4 s14
    let (s15, index_mut_back5) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output9 { start := 112#usize, «end» := 144#usize }
    let a6 ← Array.index_usize afterstate.next_frontier 2#usize
    let a7 ← dep_10 a6
    let s16 ← lift (Array.to_slice a7)
    let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
    let output10 := index_mut_back5 s17
    let (s18, index_mut_back6) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output10 { start := 144#usize, «end» := 176#usize }
    let a8 ← Array.index_usize afterstate.next_frontier 3#usize
    let a9 ← dep_10 a8
    let s19 ← lift (Array.to_slice a9)
    let s20 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s18 s19
    let output11 := index_mut_back6 s20
    let (s21, index_mut_back7) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output11 { start := 176#usize, «end» := 208#usize }
    let a10 ← Array.index_usize afterstate.next_frontier 4#usize
    let a11 ← dep_10 a10
    let s22 ← lift (Array.to_slice a11)
    let s23 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s21 s22
    let output12 := index_mut_back7 s23
    let (s24, index_mut_back8) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output12 { start := 208#usize, «end» := 240#usize }
    let a12 ← Array.index_usize afterstate.next_frontier 5#usize
    let a13 ← dep_10 a12
    let s25 ← lift (Array.to_slice a13)
    let s26 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s24 s25
    let output13 := index_mut_back8 s26
    let (s27, index_mut_back9) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output13 { start := 240#usize, «end» := 272#usize }
    let a14 ← Array.index_usize afterstate.next_frontier 6#usize
    let a15 ← dep_10 a14
    let s28 ← lift (Array.to_slice a15)
    let s29 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s27 s28
    let output14 := index_mut_back9 s29
    let (s30, index_mut_back10) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output14 { start := 272#usize, «end» := 304#usize }
    let a16 ← Array.index_usize afterstate.next_frontier 7#usize
    let a17 ← dep_10 a16
    let s31 ← lift (Array.to_slice a17)
    let s32 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s30 s31
    let output15 := index_mut_back10 s32
    let (s33, index_mut_back11) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output15 { start := 304#usize, «end» := 336#usize }
    let a18 ← Array.index_usize afterstate.next_frontier 8#usize
    let a19 ← dep_10 a18
    let s34 ← lift (Array.to_slice a19)
    let s35 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s33 s34
    let output16 := index_mut_back11 s35
    let (s36, index_mut_back12) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output16 { start := 336#usize, «end» := 368#usize }
    let a20 ← Array.index_usize afterstate.next_frontier 9#usize
    let a21 ← dep_10 a20
    let s37 ← lift (Array.to_slice a21)
    let s38 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s36 s37
    let output17 := index_mut_back12 s38
    let (s39, index_mut_back13) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output17 { start := 368#usize, «end» := 400#usize }
    let a22 ← Array.index_usize afterstate.next_frontier 10#usize
    let a23 ← dep_10 a22
    let s40 ← lift (Array.to_slice a23)
    let s41 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s39 s40
    let output18 := index_mut_back13 s41
    let (s42, index_mut_back14) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output18 { start := 400#usize, «end» := 432#usize }
    let a24 ← Array.index_usize afterstate.next_frontier 11#usize
    let a25 ← dep_10 a24
    let s43 ← lift (Array.to_slice a25)
    let s44 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s42 s43
    let output19 := index_mut_back14 s44
    let (s45, index_mut_back15) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output19 { start := 432#usize, «end» := 464#usize }
    let a26 ← Array.index_usize afterstate.next_frontier 12#usize
    let a27 ← dep_10 a26
    let s46 ← lift (Array.to_slice a27)
    let s47 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s45 s46
    let output20 := index_mut_back15 s47
    let (s48, index_mut_back16) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output20 { start := 464#usize, «end» := 496#usize }
    let a28 ← Array.index_usize afterstate.next_frontier 13#usize
    let a29 ← dep_10 a28
    let s49 ← lift (Array.to_slice a29)
    let s50 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s48 s49
    let output21 := index_mut_back16 s50
    let (s51, index_mut_back17) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output21 { start := 496#usize, «end» := 528#usize }
    let a30 ← Array.index_usize afterstate.next_frontier 14#usize
    let a31 ← dep_10 a30
    let s52 ← lift (Array.to_slice a31)
    let s53 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s51 s52
    let output22 := index_mut_back17 s53
    let (s54, index_mut_back18) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output22 { start := 528#usize, «end» := 560#usize }
    let a32 ← Array.index_usize afterstate.next_frontier 15#usize
    let a33 ← dep_10 a32
    let s55 ← lift (Array.to_slice a33)
    let s56 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s54 s55
    let output23 := index_mut_back18 s56
    let (s57, index_mut_back19) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output23 { start := 560#usize, «end» := 592#usize }
    let a34 ← Array.index_usize afterstate.next_frontier 16#usize
    let a35 ← dep_10 a34
    let s58 ← lift (Array.to_slice a35)
    let s59 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s57 s58
    let output24 := index_mut_back19 s59
    let (s60, index_mut_back20) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output24 { start := 592#usize, «end» := 624#usize }
    let a36 ← Array.index_usize afterstate.next_frontier 17#usize
    let a37 ← dep_10 a36
    let s61 ← lift (Array.to_slice a37)
    let s62 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s60 s61
    let output25 := index_mut_back20 s62
    let (s63, index_mut_back21) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output25 { start := 624#usize, «end» := 656#usize }
    let a38 ← Array.index_usize afterstate.next_frontier 18#usize
    let a39 ← dep_10 a38
    let s64 ← lift (Array.to_slice a39)
    let s65 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s63 s64
    let output26 := index_mut_back21 s65
    let (s66, index_mut_back22) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output26 { start := 656#usize, «end» := 688#usize }
    let a40 ← Array.index_usize afterstate.next_frontier 19#usize
    let a41 ← dep_10 a40
    let s67 ← lift (Array.to_slice a41)
    let s68 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s66 s67
    let output27 := index_mut_back22 s68
    ok (core.result.Result.Ok output27)
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array Std.U8 688#usize) (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual





theorem link_90 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 := by
  have h : @context_90 (@AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical) (@AspisS6SourceCodec.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION) (@AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION) (@AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate) (@AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC) (@AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION) = @context_90 (@AspisS6FiveUnrolledCodec.aspis_statement.atomic_statement.encode_digest_canonical) (@AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION) (@AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION) (@AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate) (@AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC) (@AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION) := by
    rw [link_10 unused, link_13 unused, link_81 unused, link_87 unused, link_88 unused, link_89 unused]
  exact h

#print axioms link_90

theorem link_91 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 (AspisS6FiveUnrolledCodec.StdOptions.ops unused) := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_2 unused, link_3 unused, link_25 unused, link_26 unused, link_28 unused, link_29 unused, link_68 unused, link_70 unused, link_83 unused, link_84 unused, link_85 unused, link_86 unused, link_90 unused]
  all_goals rfl

#print axioms link_91

theorem link_92 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  all_goals rfl

#print axioms link_92

theorem link_93 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1 = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1 := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1 AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_92 unused]
  all_goals rfl

#print axioms link_93

theorem link_94 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  all_goals rfl

#print axioms link_94

theorem link_95 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1 = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1 := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1 AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_94 unused]
  all_goals rfl

#print axioms link_95

theorem link_96 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  all_goals rfl

#print axioms link_96

theorem link_97 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_96 unused]
  all_goals rfl

#print axioms link_97

theorem link_98 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops]
  all_goals rfl

#print axioms link_98

theorem link_99 (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    @AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 = @AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 := by
  unfold AspisS6SourceCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops, link_98 unused]
  all_goals rfl

#print axioms link_99

end AspisS6SourceCodec.Links
