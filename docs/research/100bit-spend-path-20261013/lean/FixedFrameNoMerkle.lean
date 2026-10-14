import R1CanonicalByteAddress
import R1CanonicalOracleLog
import R1MerkleLogExtension
import R1MerkleNodeCodec
import R1MerkleLeafCodec

/-! A fixed byte frame whose length differs from the node and leaf grammar
lengths cannot alter the finite recorded Merkle tables. -/
set_option autoImplicit false
namespace AspisR1.FixedFrameNoMerkle

open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalByteAddress CanonicalOracleLog

theorem node_parse_none_of_length_ne (bs : Bytes) (hlen : bs.length ≠ 257) :
    MerkleNodeCodec.parse bs = none := by
  cases hparse : MerkleNodeCodec.parse bs with
  | none => rfl
  | some children =>
      have hbytes := MerkleNodeCodec.parse_sound hparse
      have hlength := congrArg List.length hbytes
      rw [Merkle32Path.nodeInput_length] at hlength
      have heq : bs.length = 257 := by omega
      exact (hlen heq).elim

theorem leaf_parse_none_of_length_ne (tag : Merkle32Path.Byte) (width : Nat)
    (bs : Bytes) (hlen : bs.length ≠ width + 34) :
    MerkleLeafCodec.parse tag width bs = none := by
  cases hparse : MerkleLeafCodec.parse tag width bs with
  | none => rfl
  | some data =>
      rcases MerkleLeafCodec.parse_sound tag width bs data hparse with
        ⟨hwidth, hsalt, hbytes⟩
      have hlength := congrArg List.length hbytes
      rw [Merkle32Leaf.leaf_input_length tag data.1 data.2 hsalt] at hlength
      have heq : bs.length = width + 34 := by omega
      exact (hlen heq).elim

theorem singleton_byteLog {L : Nat} (bs : Bytes) (hfits : bs.length ≤ L)
    (answer : State) :
    CanonicalOracleLog.byteLog [(Addr.ofBytes bs hfits, answer)] = [(bs, answer)] := by
  have hcanonical : Canonical (Addr.ofBytes bs hfits) :=
    CanonicalByteAddress.canonical_ofBytes bs hfits
  have hbytes : (Addr.ofBytes bs hfits).toBytes = bs := Addr.toBytes_ofBytes bs hfits
  simp [CanonicalOracleLog.byteLog, CanonicalOracleLog.canonicalTrace,
    MerkleRecordedTargets.byteLog, hcanonical, hbytes]

theorem nodes_unchanged {L : Nat} (pre : List (Addr L × State))
    (bs : Bytes) (hfits : bs.length ≤ L) (answer : State)
    (hnode : MerkleNodeCodec.parse bs = none) :
    MerkleRecordedLog.nodes
        (CanonicalOracleLog.byteLog (pre ++ [(Addr.ofBytes bs hfits, answer)])) =
      MerkleRecordedLog.nodes (CanonicalOracleLog.byteLog pre) := by
  rw [MerkleLogExtension.canonical_byteLog_append, singleton_byteLog,
    MerkleLogExtension.nodes_append]
  simp [MerkleRecordedLog.nodes, hnode]

theorem leaves_unchanged {L : Nat} (tag : Merkle32Path.Byte) (width : Nat)
    (pre : List (Addr L × State)) (bs : Bytes) (hfits : bs.length ≤ L)
    (answer : State) (hleaf : MerkleLeafCodec.parse tag width bs = none) :
    MerkleRecordedLog.leaves tag width
        (CanonicalOracleLog.byteLog (pre ++ [(Addr.ofBytes bs hfits, answer)])) =
      MerkleRecordedLog.leaves tag width (CanonicalOracleLog.byteLog pre) := by
  rw [MerkleLogExtension.canonical_byteLog_append, singleton_byteLog,
    MerkleLogExtension.leaves_append]
  simp [MerkleRecordedLog.leaves, hleaf]

theorem recover_unchanged {L : Nat} (tag : Merkle32Path.Byte) (width : Nat)
    (pre : List (Addr L × State)) (bs : Bytes) (hfits : bs.length ≤ L)
    (answer : State) (slots : List (Fin 8)) (root : Merkle32Path.Digest)
    (hnode : MerkleNodeCodec.parse bs = none)
    (hleaf : MerkleLeafCodec.parse tag width bs = none) :
    MerkleLeafRecovery.recover
      (MerkleRecordedLog.nodes
        (CanonicalOracleLog.byteLog (pre ++ [(Addr.ofBytes bs hfits, answer)])))
      (MerkleRecordedLog.leaves tag width
        (CanonicalOracleLog.byteLog (pre ++ [(Addr.ofBytes bs hfits, answer)])))
      slots root =
    MerkleLeafRecovery.recover
      (MerkleRecordedLog.nodes (CanonicalOracleLog.byteLog pre))
      (MerkleRecordedLog.leaves tag width (CanonicalOracleLog.byteLog pre))
      slots root := by
  rw [nodes_unchanged pre bs hfits answer hnode,
    leaves_unchanged tag width pre bs hfits answer hleaf]

theorem recover_unchanged_of_length_ne {L : Nat}
    (tag : Merkle32Path.Byte) (width : Nat)
    (pre : List (Addr L × State)) (bs : Bytes) (hfits : bs.length ≤ L)
    (answer : State) (slots : List (Fin 8)) (root : Merkle32Path.Digest)
    (hnode : bs.length ≠ 257) (hleaf : bs.length ≠ width + 34) :
    MerkleLeafRecovery.recover
      (MerkleRecordedLog.nodes
        (CanonicalOracleLog.byteLog (pre ++ [(Addr.ofBytes bs hfits, answer)])))
      (MerkleRecordedLog.leaves tag width
        (CanonicalOracleLog.byteLog (pre ++ [(Addr.ofBytes bs hfits, answer)])))
      slots root =
    MerkleLeafRecovery.recover
      (MerkleRecordedLog.nodes (CanonicalOracleLog.byteLog pre))
      (MerkleRecordedLog.leaves tag width (CanonicalOracleLog.byteLog pre))
      slots root := by
  exact recover_unchanged tag width pre bs hfits answer slots root
    (node_parse_none_of_length_ne bs hnode)
    (leaf_parse_none_of_length_ne tag width bs hleaf)

#print axioms node_parse_none_of_length_ne
#print axioms leaf_parse_none_of_length_ne
#print axioms singleton_byteLog
#print axioms nodes_unchanged
#print axioms leaves_unchanged
#print axioms recover_unchanged
#print axioms recover_unchanged_of_length_ne

end AspisR1.FixedFrameNoMerkle
