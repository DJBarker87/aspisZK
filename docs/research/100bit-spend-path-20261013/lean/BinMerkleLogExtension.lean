import BinMerkleRecordedLog
import BinMerkleLeafRecovery
import Mathlib.Data.List.Basic

/-! Append stability for the finite recorded Merkle log and its first-match
lookups. These are list plumbing facts only. -/
set_option autoImplicit false
namespace AspisR1.BinMerkleLogExtension

open AspisR1.BinMerkle32Path
open AspisR1.BinMerkleTable
open AspisR1.BinMerkleLeafRecovery

variable {L : Nat}

theorem nodes_append (log extra : AspisR1.BinMerkleRecordedLog.Log) :
    AspisR1.BinMerkleRecordedLog.nodes (log ++ extra) =
      AspisR1.BinMerkleRecordedLog.nodes log ++ AspisR1.BinMerkleRecordedLog.nodes extra := by
  simp [AspisR1.BinMerkleRecordedLog.nodes, List.filterMap_append]

theorem leaves_append (tag : AspisR1.BinMerkle32Path.Byte) (width : Nat)
    (log extra : AspisR1.BinMerkleRecordedLog.Log) :
    AspisR1.BinMerkleRecordedLog.leaves tag width (log ++ extra) =
      AspisR1.BinMerkleRecordedLog.leaves tag width log ++
        AspisR1.BinMerkleRecordedLog.leaves tag width extra := by
  simp [AspisR1.BinMerkleRecordedLog.leaves, List.filterMap_append]

theorem lookup_append {nodes extra : Nodes} {digest : Digest} {children : Children}
    (h : AspisR1.BinMerkleTable.lookup nodes digest = some children) :
    AspisR1.BinMerkleTable.lookup (nodes ++ extra) digest = some children := by
  induction nodes with
  | nil => simp [AspisR1.BinMerkleTable.lookup] at h
  | cons entry rest ih =>
      rcases entry with ⟨cs, recorded⟩
      by_cases heq : recorded = digest
      · simp [AspisR1.BinMerkleTable.lookup, heq] at h ⊢
        exact h
      · have hrest : AspisR1.BinMerkleTable.lookup rest digest = some children := by
          simpa [AspisR1.BinMerkleTable.lookup, heq] using h
        simpa [AspisR1.BinMerkleTable.lookup, heq] using ih hrest

theorem lookupLeaf_append {leaves extra : Leaves} {digest : Digest} {data : LeafData}
    (h : AspisR1.BinMerkleLeafRecovery.lookupLeaf leaves digest = some data) :
    AspisR1.BinMerkleLeafRecovery.lookupLeaf (leaves ++ extra) digest = some data := by
  induction leaves with
  | nil => simp [AspisR1.BinMerkleLeafRecovery.lookupLeaf] at h
  | cons entry rest ih =>
      rcases entry with ⟨recorded, output⟩
      by_cases heq : output = digest
      · simp [AspisR1.BinMerkleLeafRecovery.lookupLeaf, heq] at h ⊢
        exact h
      · have hrest : AspisR1.BinMerkleLeafRecovery.lookupLeaf rest digest = some data := by
          simpa [AspisR1.BinMerkleLeafRecovery.lookupLeaf, heq] using h
        simpa [AspisR1.BinMerkleLeafRecovery.lookupLeaf, heq] using ih hrest

theorem walk_append (nodes extra : Nodes) :
    ∀ (slots : List (Fin 2)) (root digest : Digest),
      AspisR1.BinMerkleTable.walk nodes slots root = some digest →
      AspisR1.BinMerkleTable.walk (nodes ++ extra) slots root = some digest := by
  intro slots
  induction slots with
  | nil =>
      intro root digest h
      simpa [AspisR1.BinMerkleTable.walk] using h
  | cons slot slots ih =>
      intro root digest h
      cases hwalk : AspisR1.BinMerkleTable.walk nodes slots root with
      | none => simp [AspisR1.BinMerkleTable.walk, hwalk] at h
      | some parent =>
          have hmap :
              (AspisR1.BinMerkleTable.lookup nodes parent).map (fun cs => cs slot) =
                some digest := by
            simpa [AspisR1.BinMerkleTable.walk, hwalk] using h
          cases hlookup : AspisR1.BinMerkleTable.lookup nodes parent with
          | none => simp [hlookup] at hmap
          | some cs =>
              have hslot : cs slot = digest := by simpa [hlookup] using hmap
              have hrec := ih root parent hwalk
              have hlookup' := lookup_append (extra := extra) hlookup
              simp [AspisR1.BinMerkleTable.walk, hrec, hlookup', hslot]

theorem recover_append (nodes extraNodes : Nodes) (leaves extraLeaves : Leaves)
    (slots : List (Fin 2)) (root : Digest) (data : LeafData)
    (h : AspisR1.BinMerkleLeafRecovery.recover nodes leaves slots root = some data) :
    AspisR1.BinMerkleLeafRecovery.recover (nodes ++ extraNodes) (leaves ++ extraLeaves)
      slots root = some data := by
  cases hwalk : AspisR1.BinMerkleTable.walk nodes slots root with
  | none => simp [AspisR1.BinMerkleLeafRecovery.recover, hwalk] at h
  | some digest =>
      have hlookup : AspisR1.BinMerkleLeafRecovery.lookupLeaf leaves digest = some data := by
        simpa [AspisR1.BinMerkleLeafRecovery.recover, hwalk] using h
      have hwalk' := walk_append nodes extraNodes slots root digest hwalk
      have hlookup' := lookupLeaf_append (extra := extraLeaves) hlookup
      simp [AspisR1.BinMerkleLeafRecovery.recover, hwalk', hlookup']


#print axioms nodes_append
#print axioms leaves_append
#print axioms lookup_append
#print axioms lookupLeaf_append
#print axioms walk_append
#print axioms recover_append
end AspisR1.BinMerkleLogExtension
