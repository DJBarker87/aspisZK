import RPz7_S6NativeLateEncodeSuccessV1
import S6LateWriteFramesV1
import S6ShortSlicesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeLateHeaderLayout
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeLateDecoderSplit.Frames

def header_bytes : List U8 := AspisS6SliceFrame.late_header
  POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val
  POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT 0#u8
  (core.num.U16.to_le_bytes 32#u16).val (core.num.U32.to_le_bytes 800#u32).val
  (core.num.U32.to_le_bytes 688#u32).val (core.num.U32.to_le_bytes 1520#u32).val

theorem header_length : header_bytes.length=32 := by
  simp only [header_bytes,AspisS6SliceFrame.late_header,List.length_append,
    List.length_cons,List.length_nil,List.length_replicate,
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.property,
    (core.num.U16.to_le_bytes 32#u16).property,(core.num.U32.to_le_bytes 800#u32).property,
    (core.num.U32.to_le_bytes 688#u32).property,(core.num.U32.to_le_bytes 1520#u32).property]
  decide

theorem header_prefix (raw : Array U8 1520#usize) (frame : header_frame raw) :
    header_bytes=raw.val.take 32 := by
  rcases frame with ⟨magic,version,count,header,snapshot,afterstate,total,reserved⟩
  rcases reserved with ⟨h24,h25,h26,h27,h28,h29,h30,h31⟩
  have hm : raw.val.take 8=POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val := by
    simpa [List.slice] using magic
  have two := AspisS6SliceFrame.slice_two raw.val 8 (by rw [raw.property]; decide)
  have eight := AspisS6SliceFrame.slice_eight raw.val 24 (by rw [raw.property]; decide)
  have first := AspisS6SliceFrame.take_append_slice raw.val 8 10 (by decide)
  rw [hm,two,version,count] at first
  have h10 : (POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val++[POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION])++
      [POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT]=raw.val.take 10 := by
    simpa only [List.append_assoc,List.singleton_append] using first
  have hz : List.slice 24 32 raw.val=List.replicate 8 0#u8 := by
    rw [eight,h24,h25,h26,h27,h28,h29,h30,h31]
    rfl
  unfold header_bytes AspisS6SliceFrame.late_header
  rw [h10,header,snapshot,afterstate,total,←hz]
  rw [AspisS6SliceFrame.take_append_slice raw.val 10 12 (by decide),
    AspisS6SliceFrame.take_append_slice raw.val 12 16 (by decide),
    AspisS6SliceFrame.take_append_slice raw.val 16 20 (by decide),
    AspisS6SliceFrame.take_append_slice raw.val 20 24 (by decide),
    AspisS6SliceFrame.take_append_slice raw.val 24 32 (by decide)]

theorem cast16_32 : UScalar.cast .U16 32#usize=32#u16 := by scalar_tac
#print axioms cast16_32
theorem cast32_800 : UScalar.cast .U32 800#usize=800#u32 := by scalar_tac
#print axioms cast32_800
theorem cast32_688 : UScalar.cast .U32 688#usize=688#u32 := by scalar_tac
#print axioms cast32_688
theorem cast32_1520 : UScalar.cast .U32 1520#usize=1520#u32 := by scalar_tac
#print axioms cast32_1520

#print axioms header_length
#print axioms header_prefix
end AspisS6NativeLateHeaderLayout
