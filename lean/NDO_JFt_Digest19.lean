import NDO_JFu_PublicDigest19
import NDO_JFt_DigestInjective
import NDO_JFu_PublicRange
set_option autoImplicit false
namespace AspisR1.JFt_Digest19
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,1299980413#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest JFu_PublicDigest19.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=JFu_DigestSliceFacts.source JFu_PublicDigest19.window
    JFu_PublicDigest19.length JFu_PublicDigest19.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=JFu_PublicDigest19.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,JFu_PublicDigest19.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : JFu_PublicRange.segment 880 32 (by decide)=JFu_PublicDigest19.window := by
  apply Subtype.ext
  dsimp only [JFu_PublicRange.segment,JFu_PublicDigest19.window]
  exact JFu_PublicDigest19.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (JFu_PublicRange.segment 880 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : JFu_DigestCanonical.Canonical value :=
  JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.JFt_Digest19
