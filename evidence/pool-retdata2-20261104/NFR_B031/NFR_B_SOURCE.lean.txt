import NFR_AfterstateForward
set_option autoImplicit false
noncomputable section
namespace NFR_ResultForwardHelpers
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K NFO_ResultLayout
abbrev Output := NFO_ResultLayout.Output
def encoded (r : Output) : Slice U8 := (NFO_ResultLayout.bytes r).to_slice
theorem layout (r : Output) :
    (encoded r).val = [65#u8,83#u8,82#u8,56#u8,1#u8,kind r.transition_kind,1#u8,r.output_lane] ++
      r.master_account.val ++ r.selected_lane_account.val ++
      (DigestBytes.bytes r.nullifier).val ++ (AfterstateEncoding.bytes r.verified_afterstate).val :=
  NFO_ResultLayout.stores_layout _ _ _ _ _ _
#print axioms layout

theorem width32 (a : Array U8 32#usize) : a.val.length = 32 := a.property
theorem width688 (a : Array U8 688#usize) : a.val.length = 688 := a.property
#print axioms width32
#print axioms width688

theorem nullifier_domain (s : NEU_EmitModel.Statement)
    (valid : pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    NBD_DigestInduction.Canonical (ResultAdmission.value s).nullifier := by
  have lane := StatementLane.lane s valid
  change NBD_DigestInduction.Canonical (StatementChecks.nullifier s)
  by_contra bad
  unfold pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 at lane
  rw [NBD_DigestInduction.same_scanner,NBD_DigestInduction.source] at lane
  simp [bad] at lane
#print axioms nullifier_domain

theorem head (r : Output) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      (encoded r) {«end»:=4#usize} =
      ok pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC.to_slice := by
  simp [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index,encoded,Array.to_slice,
    Slice.len,Slice.length,(NFO_ResultLayout.bytes r).property,layout,
    NFO_ResultLayout.bytes,NFO_ResultLayout.stores_layout,List.slice,
    pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC,Array.make]
#print axioms head

theorem get4 (r : Output) : Slice.index_usize (encoded r) 4#usize = ok (1#u8) := by
  simp [Slice.index_usize,encoded,Array.to_slice,Slice.length,
    (NFO_ResultLayout.bytes r).property,NFO_ResultLayout.bytes,NFO_ResultLayout.stores_layout]
#print axioms get4

theorem get5 (r : Output) : Slice.index_usize (encoded r) 5#usize = ok (kind r.transition_kind) := by
  simp [Slice.index_usize,encoded,Array.to_slice,Slice.length,
    (NFO_ResultLayout.bytes r).property,NFO_ResultLayout.bytes,NFO_ResultLayout.stores_layout]
#print axioms get5

theorem get6 (r : Output) : Slice.index_usize (encoded r) 6#usize = ok (1#u8) := by
  simp [Slice.index_usize,encoded,Array.to_slice,Slice.length,
    (NFO_ResultLayout.bytes r).property,NFO_ResultLayout.bytes,NFO_ResultLayout.stores_layout]
#print axioms get6

theorem get7 (r : Output) : Slice.index_usize (encoded r) 7#usize = ok (r.output_lane) := by
  simp [Slice.index_usize,encoded,Array.to_slice,Slice.length,
    (NFO_ResultLayout.bytes r).property,NFO_ResultLayout.bytes,NFO_ResultLayout.stores_layout]
#print axioms get7

theorem master_range (r : Output) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (encoded r) {start:=8#usize,«end»:=40#usize} =
      ok (r.master_account).to_slice := by
  apply NFR_AfterstateForwardHelpers.range
  · decide
  · simp [encoded,Array.to_slice,(NFO_ResultLayout.bytes r).property]
  · rw [layout]
    simp [List.slice,List.drop_append,List.take_append,width32,width688]
#print axioms master_range

theorem selected_range (r : Output) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (encoded r) {start:=40#usize,«end»:=72#usize} =
      ok (r.selected_lane_account).to_slice := by
  apply NFR_AfterstateForwardHelpers.range
  · decide
  · simp [encoded,Array.to_slice,(NFO_ResultLayout.bytes r).property]
  · rw [layout]
    simp [List.slice,List.drop_append,List.take_append,width32,width688]
#print axioms selected_range

theorem digest_range (r : Output) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (encoded r) {start:=72#usize,«end»:=104#usize} =
      ok (DigestBytes.bytes r.nullifier).to_slice := by
  apply NFR_AfterstateForwardHelpers.range
  · decide
  · simp [encoded,Array.to_slice,(NFO_ResultLayout.bytes r).property]
  · rw [layout]
    simp [List.slice,List.drop_append,List.take_append,width32,width688]
#print axioms digest_range

theorem afterstate_range (r : Output) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      (encoded r) {start:=104#usize} =
      ok (AfterstateEncoding.bytes r.verified_afterstate).to_slice := by
  simp [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index,Slice.len,Slice.length,
    show (encoded r).val.length = 792 from (NFO_ResultLayout.bytes r).property,
    Array.to_slice,Slice.drop,List.slice,layout,List.drop_append,List.take_append,width32,width688]
#print axioms afterstate_range

theorem kind_roundtrip (k : pool_v1.historical_anchor.PoolV1TransitionKind) :
    pool_v1.pair_forest_terminal.transition_kind (kind k) = ok (.Ok k) := by
  cases k <;> rfl
#print axioms kind_roundtrip
end NFR_ResultForwardHelpers
