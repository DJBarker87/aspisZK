import NDO_JFu_PublicDigest05
import NDO_JFt_DigestInjective
import NDO_JFu_PublicRange
set_option autoImplicit false
namespace AspisR1.JFt_Digest05
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1603344092#u32,1242405009#u32,1153352827#u32,393697509#u32,714169239#u32,2094351560#u32,55834509#u32,664305674#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest JFu_PublicDigest05.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=JFu_DigestSliceFacts.source JFu_PublicDigest05.window
    JFu_PublicDigest05.length JFu_PublicDigest05.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=JFu_PublicDigest05.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,JFu_PublicDigest05.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : JFu_PublicRange.segment 432 32 (by decide)=JFu_PublicDigest05.window := by
  apply Subtype.ext
  exact JFu_PublicDigest05.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (JFu_PublicRange.segment 432 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : JFu_DigestCanonical.Canonical value :=
  JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.JFt_Digest05
