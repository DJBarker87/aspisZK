import NDO_JFu_PublicDigest02
import NDO_JFt_DigestInjective
import NDO_JFu_PublicRange
set_option autoImplicit false
namespace AspisR1.JFt_Digest02
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [20384#u32,20401#u32,20418#u32,20435#u32,20452#u32,20469#u32,20486#u32,20503#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest JFu_PublicDigest02.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=JFu_DigestSliceFacts.source JFu_PublicDigest02.window
    JFu_PublicDigest02.length JFu_PublicDigest02.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=JFu_PublicDigest02.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,JFu_PublicDigest02.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : JFu_PublicRange.segment 336 32 (by decide)=JFu_PublicDigest02.window := by
  apply Subtype.ext
  exact JFu_PublicDigest02.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (JFu_PublicRange.segment 336 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : JFu_DigestCanonical.Canonical value :=
  JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.JFt_Digest02
