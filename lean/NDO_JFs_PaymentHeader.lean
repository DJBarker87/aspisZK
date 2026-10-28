import NDO_JFs_PaymentArray
import NDO_JFs_ArrayHeader
set_option autoImplicit false
namespace AspisR1.JFs_PaymentHeader
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.payment_relation

def magic : Slice U8 := ⟨JFu_PublicMeta07.bytes.take 4,by simp [JFu_PublicMeta07.bytes];scalar_tac⟩
theorem selected : JFu_PublicRange.segment 1664 4 (by decide)=magic := by
  apply Subtype.ext
  exact JFt_LocalWindow.selected 1664 8 0 4 (by decide) (by decide) _ JFu_PublicMeta07.selected

theorem magic_call : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
    JFs_PaymentArray.value {«end»:=4#usize}=ok magic := by
  simp only [JFs_PaymentArray.value,
    JFs_ArrayHeader.firstn 1664 216#usize (by decide) 4#usize (by decide),
    show (4#usize).val=4 from rfl,selected]

theorem b4 : Array.index_usize JFs_PaymentArray.value 4#usize=ok 1#u8 := by
  have h:=JFs_IndexWindow.source 1664 216 8 (by decide) 4#usize (by decide) (by decide)
    1#u8 JFu_PublicMeta07.bytes JFu_PublicMeta07.selected (by rfl)
  simpa only [JFs_PaymentArray.value,JFs_ArrayHeader.index,
    show (216#usize).val=216 from rfl] using h

theorem b5 : Array.index_usize JFs_PaymentArray.value 5#usize=ok 1#u8 := by
  have h:=JFs_IndexWindow.source 1664 216 8 (by decide) 5#usize (by decide) (by decide)
    1#u8 JFu_PublicMeta07.bytes JFu_PublicMeta07.selected (by rfl)
  simpa only [JFs_PaymentArray.value,JFs_ArrayHeader.index,
    show (216#usize).val=216 from rfl] using h

theorem b6 : Array.index_usize JFs_PaymentArray.value 6#usize=ok 1#u8 := by
  have h:=JFs_IndexWindow.source 1664 216 8 (by decide) 6#usize (by decide) (by decide)
    1#u8 JFu_PublicMeta07.bytes JFu_PublicMeta07.selected (by rfl)
  simpa only [JFs_PaymentArray.value,JFs_ArrayHeader.index,
    show (216#usize).val=216 from rfl] using h

theorem b7 : Array.index_usize JFs_PaymentArray.value 7#usize=ok 0#u8 := by
  have h:=JFs_IndexWindow.source 1664 216 8 (by decide) 7#usize (by decide) (by decide)
    0#u8 JFu_PublicMeta07.bytes JFu_PublicMeta07.selected (by rfl)
  simpa only [JFs_PaymentArray.value,JFs_ArrayHeader.index,
    show (216#usize).val=216 from rfl] using h

theorem source : require_header JFs_PaymentArray.value POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
    pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer=ok (.Ok ()) := by
  unfold require_header
  simp only [magic_call,b4,b5,b6,b7,bind_tc_ok]
  unfold POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC POOL_V1_PAYMENT_STATEMENT_VERSION
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  rfl

#print axioms selected
#print axioms magic_call
#print axioms b4
#print axioms b5
#print axioms b6
#print axioms b7
#print axioms source
end AspisR1.JFs_PaymentHeader
