import JHb_S2K_ResultBytes
import NDO_JHb_S2K_StatementAdmission

/-! Exact source field-boundary reference. The nullifier and afterstate inputs
are sub-encoder bytes, to be instantiated with their SAME source values. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.ResultEncoding

def stores (out : Array U8 792#usize) (master selected nullifier : Array U8 32#usize)
    (kind lane : U8) (afterstate : Array U8 688#usize) : Array U8 792#usize :=
  ⟨(((((((((out.val.setSlice! 0 [65#u8,83#u8,82#u8,56#u8]).set
      4 1#u8).set 5 kind).set 6 1#u8).set 7 lane).setSlice! 8 master.val).setSlice!
      40 selected.val).setSlice! 72 nullifier.val).setSlice! 104 afterstate.val), by
        simp only [List.length_setSlice!,List.length_set,out.property]⟩

theorem source_value (master selected nullifier : Array U8 32#usize)
    (kind lane : U8) (afterstate : Array U8 688#usize) :
    S2K_ResultBytes.S2K_reference_bytes master selected nullifier kind lane afterstate =
      ok (stores (Array.repeat 792#usize 0#u8) master selected nullifier kind lane afterstate) := by
  unfold S2K_ResultBytes.S2K_reference_bytes
  generalize Array.repeat 792#usize 0#u8 = output
  simp [S2K_ResultBytes.S2K_store_magic,S2K_ResultBytes.S2K_store_version,
    S2K_ResultBytes.S2K_store_kind,S2K_ResultBytes.S2K_store_digest_version,
    S2K_ResultBytes.S2K_store_lane,S2K_ResultBytes.S2K_store_master,
    S2K_ResultBytes.S2K_store_selected,S2K_ResultBytes.S2K_store_nullifier_bytes,
    S2K_ResultBytes.S2K_store_afterstate,
    S2K_ResultBytes.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC,
    S2K_ResultBytes.POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
    S2K_ResultBytes.POOL_V1_DIGEST_ENCODING_VERSION,
    S2K_ResultBytes.RESULT_MASTER_OFFSET,S2K_ResultBytes.RESULT_SELECTED_LANE_OFFSET,
    S2K_ResultBytes.RESULT_NULLIFIER_OFFSET,S2K_ResultBytes.RESULT_AFTERSTATE_OFFSET,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeFromUsizeSlice,core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    Array.to_slice,Array.from_slice,core.slice.Slice.copy_from_slice,
    Slice.length,Slice.len,Array.update,output.property,List.slice,lift,stores]
  rfl

#print axioms source_value
end AspisR1.S2K.ResultEncoding
