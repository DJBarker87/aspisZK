import NDO_JFs_PaymentArray
import NDO_JFs_Cell04
import NDO_JFs_Cell05
import NDO_JFs_Cell06
import NDO_JFs_Cell07
import NDO_JFu_PublicMeta08
import S6ZeroWordBytesV1
set_option autoImplicit false
namespace AspisR1.JFs_PaymentReads
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem cast4 : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (JFu_PublicRange.segment 1672 32 (by decide))=ok (.Ok JFs_Cell04.value) :=
  by
  apply JFt_ExactArray.cast
  dsimp only [JFu_PublicRange.segment,JFs_Cell04.value]
  exact JFs_Cell04.selected

theorem cast5 : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (JFu_PublicRange.segment 1704 32 (by decide))=ok (.Ok JFs_Cell05.value) :=
  by
  apply JFt_ExactArray.cast
  dsimp only [JFu_PublicRange.segment,JFs_Cell05.value]
  exact JFs_Cell05.selected

theorem cast6 : core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8
    (JFu_PublicRange.segment 1736 8 (by decide))=ok (.Ok JFs_Cell06.value) :=
  by
  apply JFt_ExactArray.cast
  dsimp only [JFu_PublicRange.segment,JFs_Cell06.value]
  exact JFs_Cell06.selected

theorem cast7 : core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8
    (JFu_PublicRange.segment 1808 4 (by decide))=ok (.Ok JFs_Cell07.value) :=
  by
  apply JFt_ExactArray.cast
  dsimp only [JFu_PublicRange.segment,JFs_Cell07.value]
  exact JFs_Cell07.selected

def fee : Slice U8 := ⟨JFu_PublicMeta08.bytes,by simp [JFu_PublicMeta08.bytes];scalar_tac⟩
theorem fee_selected : JFu_PublicRange.segment 1812 4 (by decide)=fee := by
  apply Subtype.ext
  dsimp only [JFu_PublicRange.segment,fee]
  exact JFu_PublicMeta08.selected

theorem fee_bytes : core.num.U32.to_le_bytes 0#u32=
    (⟨JFu_PublicMeta08.bytes,by simp [JFu_PublicMeta08.bytes]⟩ : Array U8 4#usize) := by
  apply Subtype.ext
  simpa only [JFu_PublicMeta08.bytes,List.replicate] using AspisS6ZeroWord.u32_zero

theorem fee_compare : core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) fee fee=ok false := by rfl

#print axioms cast4
#print axioms cast5
#print axioms cast6
#print axioms cast7
#print axioms fee_selected
#print axioms fee_bytes
#print axioms fee_compare
end AspisR1.JFs_PaymentReads
