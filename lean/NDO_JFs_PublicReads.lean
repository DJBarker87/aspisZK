import NDO_JFs_PublicValue
import NDO_JFt_DigestArray
set_option autoImplicit false
namespace AspisR1.JFs_PublicReads
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem cast0 : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (JFu_PublicRange.segment 8 32 (by decide))=ok (.Ok JFs_Cell00.value) := by
  apply JFt_ExactArray.cast
  dsimp only [JFu_PublicRange.segment,JFs_Cell00.value]
  exact JFs_Cell00.selected

theorem cast1 : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (JFu_PublicRange.segment 40 32 (by decide))=ok (.Ok JFs_Cell01.value) := by
  apply JFt_ExactArray.cast
  dsimp only [JFu_PublicRange.segment,JFs_Cell01.value]
  exact JFs_Cell01.selected

theorem cast2 : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (JFu_PublicRange.segment 72 32 (by decide))=ok (.Ok JFs_Cell02.value) := by
  apply JFt_ExactArray.cast
  dsimp only [JFu_PublicRange.segment,JFs_Cell02.value]
  exact JFs_Cell02.selected

theorem cast3 : core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8
    (JFu_PublicRange.segment 104 8 (by decide))=ok (.Ok JFs_Cell03.value) := by
  apply JFt_ExactArray.cast
  dsimp only [JFu_PublicRange.segment,JFs_Cell03.value]
  exact JFs_Cell03.selected

def root : Array U8 32#usize := ⟨JFu_PublicDigest00.bytes,JFu_PublicDigest00.length⟩
theorem root_selected : (JFu_PublicRange.segment 112 32 (by decide)).val=root.val := by
  dsimp only [JFu_PublicRange.segment,root]
  exact JFu_PublicDigest00.selected

theorem root_shared : core.array.TryFromSharedArraySlice.try_from 32#usize
    (JFu_PublicRange.segment 112 32 (by decide))=ok (.Ok root) :=
  JFt_DigestArray.shared _ _ root_selected

theorem root_decode : atomic_statement.decode_digest_canonical root=ok (.Ok JFt_Digest00.value) :=
  JFt_DigestArray.source _ _ root_selected _ JFt_Digest00.source

#print axioms cast0
#print axioms cast1
#print axioms cast2
#print axioms cast3
#print axioms root_selected
#print axioms root_shared
#print axioms root_decode
end AspisR1.JFs_PublicReads
