import NDO_JFu_PublicDigests
import NDO_JFu_DigestSliceFacts
import NDO_JFu_PublicRange
set_option autoImplicit false
namespace AspisR1.JFu_PublicWindowFacts
open Aeneas Aeneas.Std Result WP
open OraclePortCompactDraft MultiproofConeCanonical

theorem source (off : Nat) (member : off ∈ JFu_PublicDigests.offsets)
    (input : Slice U8) (same : input.val=(JFx_NativeBytes.publicInput.val.drop off).take 32)
    (size : input.length=32) :
    ∃ out,AspisS6NativeSnapshotReadDigest.read_digest input=ok (.Ok out) ∧
      JFu_DigestCanonical.Canonical out ∧
      AspisS6SourceCodec.DigestContents.chunks out=(JFx_NativeBytes.publicInput.val.drop off).take 32 := by
  have canon : canonical (bytesOf input.val) := by
    rw [same]
    exact JFu_PublicDigests.canonical_windows off member
  obtain ⟨out,call,bound,contents⟩:=JFu_DigestSliceFacts.source input size canon
  exact ⟨out,call,bound,contents.trans same⟩

#print axioms source
end AspisR1.JFu_PublicWindowFacts
