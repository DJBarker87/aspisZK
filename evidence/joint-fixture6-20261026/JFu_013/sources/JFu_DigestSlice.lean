import JFu_DigestDecode
set_option autoImplicit false
namespace AspisR1.JFu_DigestSlice
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder
open OraclePortCompactDraft MultiproofConeCanonical

@[local step] theorem digest (arr : Array U8 32#usize) (canon : canonical (bytesOf arr.val)) :
    atomic_statement.decode_digest_canonical arr ⦃ out => ∃ q,out=.Ok q ⦄ := by
  obtain ⟨q,call⟩:=JFu_DigestDecode.success arr canon
  rw [call,WP.spec_ok]
  exact ⟨q,rfl⟩

theorem success (bytes : Slice U8) (size : bytes.length=32)
    (canon : canonical (bytesOf bytes.val)) :
    ∃ out,AspisS6NativeSnapshotReadDigest.read_digest bytes=ok (.Ok out) := by
  have spec : AspisS6NativeSnapshotReadDigest.read_digest bytes ⦃ out => ∃ q,out=.Ok q ⦄ := by
    unfold AspisS6NativeSnapshotReadDigest.read_digest
    step*
  obtain ⟨out,call,q,same⟩:=WP.spec_imp_exists spec
  exact ⟨q,by rw [same] at call;exact call⟩

#print axioms digest
#print axioms success
#print core.array.TryFromSharedArraySlice.try_from
end AspisR1.JFu_DigestSlice
