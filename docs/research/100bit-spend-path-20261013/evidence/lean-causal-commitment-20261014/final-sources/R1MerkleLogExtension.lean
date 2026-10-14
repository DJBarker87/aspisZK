import R1CanonicalOracleLog
import R1MerkleLeafRecovery
import Mathlib.Data.List.Basic

/-! Append stability for the finite recorded Merkle log and its first-match
lookups. These are list plumbing facts only. -/
set_option autoImplicit false
namespace AspisR1.MerkleLogExtension

open AspisR1.Merkle32Path
open AspisR1.MerkleTable
open AspisR1.MerkleLeafRecovery

variable {L : Nat}

theorem canonical_byteLog_append
    (pre post : List (FS2.Duplex.Addr L × AspisV8R19.SourceDuplexStep.State)) :
    AspisR1.CanonicalOracleLog.byteLog (pre ++ post) =
      AspisR1.CanonicalOracleLog.byteLog pre ++ AspisR1.CanonicalOracleLog.byteLog post := by
  simp [AspisR1.CanonicalOracleLog.byteLog,
    AspisR1.MerkleRecordedTargets.byteLog,
    AspisR1.CanonicalOracleLog.canonicalTrace]

theorem nodes_append (log extra : AspisR1.MerkleRecordedLog.Log) :
    AspisR1.MerkleRecordedLog.nodes (log ++ extra) =
      AspisR1.MerkleRecordedLog.nodes log ++ AspisR1.MerkleRecordedLog.nodes extra := by
  simp [AspisR1.MerkleRecordedLog.nodes, List.filterMap_append]

theorem leaves_append (tag : AspisR1.Merkle32Path.Byte) (width : Nat)
    (log extra : AspisR1.MerkleRecordedLog.Log) :
    AspisR1.MerkleRecordedLog.leaves tag width (log ++ extra) =
      AspisR1.MerkleRecordedLog.leaves tag width log ++
        AspisR1.MerkleRecordedLog.leaves tag width extra := by
  simp [AspisR1.MerkleRecordedLog.leaves, List.filterMap_append]

theorem lookup_append {nodes extra : Nodes} {digest : Digest} {children : Children}
    (h : AspisR1.MerkleTable.lookup nodes digest = some children) :
    AspisR1.MerkleTable.lookup (nodes ++ extra) digest = some children := by
  induction nodes with
  | nil => simp [AspisR1.MerkleTable.lookup] at h
  | cons entry rest ih =>
      rcases entry with ⟨cs, recorded⟩
      by_cases heq : recorded = digest
      · simp [AspisR1.MerkleTable.lookup, heq] at h ⊢
        exact h
      · have hrest : AspisR1.MerkleTable.lookup rest digest = some children := by
          simpa [AspisR1.MerkleTable.lookup, heq] using h
        simpa [AspisR1.MerkleTable.lookup, heq] using ih hrest

theorem lookupLeaf_append {leaves extra : Leaves} {digest : Digest} {data : LeafData}
    (h : AspisR1.MerkleLeafRecovery.lookupLeaf leaves digest = some data) :
    AspisR1.MerkleLeafRecovery.lookupLeaf (leaves ++ extra) digest = some data := by
  induction leaves with
  | nil => simp [AspisR1.MerkleLeafRecovery.lookupLeaf] at h
  | cons entry rest ih =>
      rcases entry with ⟨recorded, output⟩
      by_cases heq : output = digest
      · simp [AspisR1.MerkleLeafRecovery.lookupLeaf, heq] at h ⊢
        exact h
      · have hrest : AspisR1.MerkleLeafRecovery.lookupLeaf rest digest = some data := by
          simpa [AspisR1.MerkleLeafRecovery.lookupLeaf, heq] using h
        simpa [AspisR1.MerkleLeafRecovery.lookupLeaf, heq] using ih hrest

theorem walk_append (nodes extra : Nodes) :
    ∀ (slots : List (Fin 8)) (root digest : Digest),
      AspisR1.MerkleTable.walk nodes slots root = some digest →
      AspisR1.MerkleTable.walk (nodes ++ extra) slots root = some digest := by
  intro slots
  induction slots with
  | nil =>
      intro root digest h
      simpa [AspisR1.MerkleTable.walk] using h
  | cons slot slots ih =>
      intro root digest h
      cases hwalk : AspisR1.MerkleTable.walk nodes slots root with
      | none => simp [AspisR1.MerkleTable.walk, hwalk] at h
      | some parent =>
          have hmap :
              (AspisR1.MerkleTable.lookup nodes parent).map (fun cs => cs slot) =
                some digest := by
            simpa [AspisR1.MerkleTable.walk, hwalk] using h
          cases hlookup : AspisR1.MerkleTable.lookup nodes parent with
          | none => simp [hlookup] at hmap
          | some cs =>
              have hslot : cs slot = digest := by simpa [hlookup] using hmap
              have hrec := ih root parent hwalk
              have hlookup' := lookup_append (extra := extra) hlookup
              simp [AspisR1.MerkleTable.walk, hrec, hlookup', hslot]

theorem recover_append (nodes extraNodes : Nodes) (leaves extraLeaves : Leaves)
    (slots : List (Fin 8)) (root : Digest) (data : LeafData)
    (h : AspisR1.MerkleLeafRecovery.recover nodes leaves slots root = some data) :
    AspisR1.MerkleLeafRecovery.recover (nodes ++ extraNodes) (leaves ++ extraLeaves)
      slots root = some data := by
  cases hwalk : AspisR1.MerkleTable.walk nodes slots root with
  | none => simp [AspisR1.MerkleLeafRecovery.recover, hwalk] at h
  | some digest =>
      have hlookup : AspisR1.MerkleLeafRecovery.lookupLeaf leaves digest = some data := by
        simpa [AspisR1.MerkleLeafRecovery.recover, hwalk] using h
      have hwalk' := walk_append nodes extraNodes slots root digest hwalk
      have hlookup' := lookupLeaf_append (extra := extraLeaves) hlookup
      simp [AspisR1.MerkleLeafRecovery.recover, hwalk', hlookup']

#print axioms canonical_byteLog_append
#print axioms nodes_append
#print axioms leaves_append
#print axioms lookup_append
#print axioms lookupLeaf_append
#print axioms walk_append
#print axioms recover_append

end AspisR1.MerkleLogExtension
