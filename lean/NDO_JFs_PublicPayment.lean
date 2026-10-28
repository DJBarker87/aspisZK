import NDO_JFs_SuffixRead
import NDO_JFs_PaymentDecode
import NDO_JFs_PublicValue
set_option autoImplicit false
namespace AspisR1.JFs_PublicPayment
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

theorem suffix : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
    JFx_NativeBytes.publicInput {start:=1664#usize}=ok JFu_PublicRange.payment := by
  apply JFs_SuffixRead.source _ _ (by rw [JFu_PublicHeader.length];decide)
  dsimp only [JFu_PublicRange.payment,JFu_PublicRange.segment]
  simp only [show (1664#usize).val=1664 from rfl]
  symm
  apply List.take_of_length_le
  rw [List.length_drop]
  have h : JFx_NativeBytes.publicInput.val.length=1880 := JFu_PublicHeader.length
  rw [h]

theorem source : decode_transfer_statement_boxed_v1 JFs_PublicValue.common JFu_PublicRange.payment=
    ok (.Ok JFs_PublicValue.value) := by
  unfold decode_transfer_statement_boxed_v1
  rw [JFs_PaymentDecode.source]
  rfl

#print axioms suffix
#print axioms source
end AspisR1.JFs_PublicPayment
