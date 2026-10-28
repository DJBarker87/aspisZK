import NDO_JFu_PublicDigest31
import NDO_JFt_DigestInjective
import NDO_JFu_PublicRange
set_option autoImplicit false
namespace AspisR1.JFt_Digest31
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,553704718#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest JFu_PublicDigest31.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=JFu_DigestSliceFacts.source JFu_PublicDigest31.window
    JFu_PublicDigest31.length JFu_PublicDigest31.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=JFu_PublicDigest31.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,JFu_PublicDigest31.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : JFu_PublicRange.segment 1280 32 (by decide)=JFu_PublicDigest31.window := by
  apply Subtype.ext
  dsimp only [JFu_PublicRange.segment,JFu_PublicDigest31.window]
  exact JFu_PublicDigest31.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (JFu_PublicRange.segment 1280 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : JFu_DigestCanonical.Canonical value :=
  JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.JFt_Digest31
