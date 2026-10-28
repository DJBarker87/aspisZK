import NDO_JFu_DigestSliceCanonical
set_option autoImplicit false
namespace AspisR1.JFu_DigestSliceFacts
open Aeneas Aeneas.Std Result WP
open OraclePortCompactDraft MultiproofConeCanonical

theorem source (bytes : Slice U8) (size : bytes.length=32)
    (canon : canonical (bytesOf bytes.val)) :
    ∃ out,AspisS6NativeSnapshotReadDigest.read_digest bytes=ok (.Ok out) ∧
      JFu_DigestCanonical.Canonical out ∧
      AspisS6SourceCodec.DigestContents.chunks out=bytes.val := by
  obtain ⟨out,call⟩:=JFu_DigestSlice.success bytes size canon
  have bound:=JFu_DigestSliceCanonical.source bytes out call
  obtain ⟨result,read,post⟩:=WP.spec_imp_exists (AspisS6NativeSnapshotReadDigest.read_digest_spec bytes size)
  have same : result=.Ok out := Result.ok.inj (read.symm.trans call)
  exact ⟨out,call,bound,post out same⟩

#print axioms source
end AspisR1.JFu_DigestSliceFacts
