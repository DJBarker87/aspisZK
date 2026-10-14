import R1MerkleRecordedLog

/-! A prior-log hash-separation premise makes parsed leaf data functional at a
digest. Input encoding, parser widths, and salt lengths are derived locally. -/
set_option autoImplicit false
namespace AspisR1.MerkleLeafRecordUnique

abbrev Byte := AspisR1.Merkle32Path.Byte
abbrev Digest := AspisR1.Merkle32Path.Digest
abbrev Log := AspisR1.MerkleRecordedLog.Log

theorem leaves_digest_unique
    (hash : List Byte → Digest) (tag : Byte) (width : Nat) (log : Log)
    (hlog : MerkleRecordedLog.Consistent hash log)
    (hsep : ∀ a b da db, (a, da) ∈ log → (b, db) ∈ log →
      hash a = hash b → a = b) :
    ∀ left right digest,
      (left, digest) ∈ MerkleRecordedLog.leaves tag width log →
      (right, digest) ∈ MerkleRecordedLog.leaves tag width log →
      left = right := by
  intro left right digest hleft hright
  obtain ⟨inputLeft, hentryLeft, hparseLeft⟩ :=
    (MerkleRecordedLog.mem_leaves).mp hleft
  obtain ⟨inputRight, hentryRight, hparseRight⟩ :=
    (MerkleRecordedLog.mem_leaves).mp hright
  have hsLeft := AspisR1.MerkleLeafCodec.parse_sound tag width inputLeft left hparseLeft
  have hsRight := AspisR1.MerkleLeafCodec.parse_sound tag width inputRight right hparseRight
  have hhashLeft := hlog inputLeft digest hentryLeft
  have hhashRight := hlog inputRight digest hentryRight
  have hinput : inputLeft = inputRight :=
    hsep inputLeft inputRight digest digest hentryLeft hentryRight
      (hhashLeft.trans hhashRight.symm)
  have hleafInput : AspisR1.Merkle32Leaf.leafInput tag left.1 left.2 =
      AspisR1.Merkle32Leaf.leafInput tag right.1 right.2 := by
    rw [hsLeft.2.2, hsRight.2.2, hinput]
  have hwidth : left.1.length = right.1.length :=
    hsLeft.1.trans hsRight.1.symm
  have hparts := AspisR1.Merkle32Leaf.leafInput_fixedWidth_injective tag
    left.1 left.2 right.1 right.2 hwidth hleafInput
  exact Prod.ext hparts.1 hparts.2

#print axioms leaves_digest_unique

end AspisR1.MerkleLeafRecordUnique
