import NDO_JFu_PublicDigest33
import NDO_JFt_DigestInjective
import NDO_JFu_PublicRange
set_option autoImplicit false
namespace AspisR1.JFt_Digest33
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,1800828893#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest JFu_PublicDigest33.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=JFu_DigestSliceFacts.source JFu_PublicDigest33.window
    JFu_PublicDigest33.length JFu_PublicDigest33.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=JFu_PublicDigest33.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,JFu_PublicDigest33.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : JFu_PublicRange.segment 1344 32 (by decide)=JFu_PublicDigest33.window := by
  apply Subtype.ext
  dsimp only [JFu_PublicRange.segment,JFu_PublicDigest33.window]
  exact JFu_PublicDigest33.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (JFu_PublicRange.segment 1344 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : JFu_DigestCanonical.Canonical value :=
  JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.JFt_Digest33
