import R1PublicInitFrame
import R1MerkleLogExtension

/-! The public initialization frame is disjoint from the literal node and
leaf input grammars by its first byte. Consequently appending that singleton
does not change the finite recorded Merkle tables. -/
set_option autoImplicit false
namespace AspisR1.InitialFrameNoMerkle

open FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.Merkle32Path AspisR1.Merkle32Leaf
open AspisR1.CanonicalByteAddress AspisR1.CanonicalOracleLog
open AspisR1.MerkleRecordedLog AspisR1.MerkleLeafRecovery

theorem node_parse_none (pubBytes : Bytes) (root : State) :
    MerkleNodeCodec.parse (PublicInitFrame.frame pubBytes root) = none := by
  cases hparse : MerkleNodeCodec.parse (PublicInitFrame.frame pubBytes root) with
  | none => rfl
  | some children =>
      have hshape := MerkleNodeCodec.parse_sound hparse
      have hheads := congrArg List.head? hshape
      have hnode : (Merkle32Path.nodeInput children).head? =
          some (0x18 : Merkle32Path.Byte) := by simp [Merkle32Path.nodeInput]
      have hframe : (PublicInitFrame.frame pubBytes root).head? =
          some (85 : Merkle32Path.Byte) := by
        simp [PublicInitFrame.frame, PublicInitFrame.pre,
          AspisR1.TrailingStateFrame.frame, PublicInitFrame.domain]
      rw [hnode, hframe] at hheads
      have hneq : (0x18 : Merkle32Path.Byte) ≠ 85 := by decide
      exact (hneq (Option.some.inj hheads)).elim

theorem leaf_parse_none (tag : Merkle32Path.Byte) (width : Nat)
    (pubBytes : Bytes) (root : State) :
    MerkleLeafCodec.parse tag width (PublicInitFrame.frame pubBytes root) = none := by
  cases hparse : MerkleLeafCodec.parse tag width (PublicInitFrame.frame pubBytes root) with
  | none => rfl
  | some data =>
      have hshape := (MerkleLeafCodec.parse_sound tag width
        (PublicInitFrame.frame pubBytes root) data hparse).2.2
      have hheads := congrArg List.head? hshape
      have hleaf : (Merkle32Leaf.leafInput tag data.1 data.2).head? =
          some (0x10 : Merkle32Path.Byte) := by simp [Merkle32Leaf.leafInput]
      have hframe : (PublicInitFrame.frame pubBytes root).head? =
          some (85 : Merkle32Path.Byte) := by
        simp [PublicInitFrame.frame, PublicInitFrame.pre,
          AspisR1.TrailingStateFrame.frame, PublicInitFrame.domain]
      rw [hleaf, hframe] at hheads
      have hneq : (0x10 : Merkle32Path.Byte) ≠ 85 := by decide
      exact (hneq (Option.some.inj hheads)).elim

theorem singleton_byteLog {L : Nat} (pubBytes : Bytes)
    (hL : 75 + pubBytes.length ≤ L) (root answer : State) :
    CanonicalOracleLog.byteLog
      [(PublicInitFrame.addr pubBytes hL root, answer)] =
        [(PublicInitFrame.frame pubBytes root, answer)] := by
  have hcanonical : CanonicalByteAddress.Canonical
      (PublicInitFrame.addr pubBytes hL root) := by
    unfold PublicInitFrame.addr
    exact CanonicalByteAddress.canonical_ofBytes _ _
  have hbytes : (PublicInitFrame.addr pubBytes hL root).toBytes =
      PublicInitFrame.frame pubBytes root := by
    simp [PublicInitFrame.addr, FS2.Duplex.Addr.toBytes_ofBytes]
  simp [CanonicalOracleLog.byteLog, CanonicalOracleLog.canonicalTrace,
    MerkleRecordedTargets.byteLog, hcanonical, hbytes]

theorem nodes_unchanged {L : Nat} (pre : List (FS2.Duplex.Addr L × State))
    (pubBytes : Bytes) (hL : 75 + pubBytes.length ≤ L) (root answer : State) :
    MerkleRecordedLog.nodes
        (CanonicalOracleLog.byteLog
          (pre ++ [(PublicInitFrame.addr pubBytes hL root, answer)])) =
      MerkleRecordedLog.nodes (CanonicalOracleLog.byteLog pre) := by
  rw [MerkleLogExtension.canonical_byteLog_append, singleton_byteLog,
    MerkleLogExtension.nodes_append]
  simp [MerkleRecordedLog.nodes, node_parse_none]

theorem leaves_unchanged {L : Nat} (tag : Merkle32Path.Byte) (width : Nat)
    (pre : List (FS2.Duplex.Addr L × State)) (pubBytes : Bytes)
    (hL : 75 + pubBytes.length ≤ L) (root answer : State) :
    MerkleRecordedLog.leaves tag width
        (CanonicalOracleLog.byteLog
          (pre ++ [(PublicInitFrame.addr pubBytes hL root, answer)])) =
      MerkleRecordedLog.leaves tag width (CanonicalOracleLog.byteLog pre) := by
  rw [MerkleLogExtension.canonical_byteLog_append, singleton_byteLog,
    MerkleLogExtension.leaves_append]
  simp [MerkleRecordedLog.leaves, leaf_parse_none]

theorem recover_unchanged {L : Nat} (tag : Merkle32Path.Byte) (width : Nat)
    (pre : List (FS2.Duplex.Addr L × State)) (pubBytes : Bytes)
    (hL : 75 + pubBytes.length ≤ L) (frameRoot answer : State)
    (slots : List (Fin 8)) (lookupRoot : Merkle32Path.Digest) :
    MerkleLeafRecovery.recover
      (MerkleRecordedLog.nodes
        (CanonicalOracleLog.byteLog
          (pre ++ [(PublicInitFrame.addr pubBytes hL frameRoot, answer)])))
      (MerkleRecordedLog.leaves tag width
        (CanonicalOracleLog.byteLog
          (pre ++ [(PublicInitFrame.addr pubBytes hL frameRoot, answer)])))
      slots lookupRoot =
    MerkleLeafRecovery.recover
      (MerkleRecordedLog.nodes (CanonicalOracleLog.byteLog pre))
      (MerkleRecordedLog.leaves tag width (CanonicalOracleLog.byteLog pre))
      slots lookupRoot := by
  rw [nodes_unchanged, leaves_unchanged]

#print axioms node_parse_none
#print axioms leaf_parse_none
#print axioms singleton_byteLog
#print axioms nodes_unchanged
#print axioms leaves_unchanged
#print axioms recover_unchanged

end AspisR1.InitialFrameNoMerkle
