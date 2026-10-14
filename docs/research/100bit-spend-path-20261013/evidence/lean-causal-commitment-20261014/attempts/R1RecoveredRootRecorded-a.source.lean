import R1MerkleRecordedLog
import R1CanonicalLogInputs

/-! A successful nonempty recorded-table walk identifies a recorded root
output. These are deterministic finite-list facts, not witness completeness. -/
set_option autoImplicit false
namespace AspisR1.RecoveredRootRecorded

open AspisR1.Merkle32Path
open AspisR1.MerkleTable
open AspisR1.MerkleLeafRecovery
open AspisR1.MerkleRecordedLog
open FS2.Duplex
open AspisV8R19.SourceDuplexStep

variable {L : Nat}

theorem walk_root_recorded (nodes : Nodes) {slots : List (Fin 8)}
    (root leaf : Digest) (hnonempty : slots ≠ [])
    (hwalk : AspisR1.MerkleTable.walk nodes slots root = some leaf) :
    ∃ cs, (cs, root) ∈ nodes := by
  cases slots with
  | nil => contradiction
  | cons slot rest =>
      cases rest with
      | nil =>
          have hmap : (AspisR1.MerkleTable.lookup nodes root).map
              (fun cs => cs slot) = some leaf := by
            simpa [AspisR1.MerkleTable.walk] using hwalk
          cases hlookup : AspisR1.MerkleTable.lookup nodes root with
          | none => simp [hlookup] at hmap
          | some cs =>
              exact ⟨cs, AspisR1.MerkleTable.lookup_mem hlookup⟩
      | cons next rest =>
          cases htail : AspisR1.MerkleTable.walk (nodes := nodes) (next :: rest) root with
          | none => simp [AspisR1.MerkleTable.walk, htail] at hwalk
          | some parent =>
              obtain ⟨cs, hrootmem⟩ :=
                walk_root_recorded nodes (next :: rest) root parent (by simp) htail
              exact ⟨cs, hrootmem⟩

theorem recover_root_recorded (log : AspisR1.MerkleRecordedLog.Log)
    (tag : AspisR1.Merkle32Path.Byte) (width : Nat) (slots : List (Fin 8))
    (root : Digest) (data : LeafData) (hnonempty : slots ≠ [])
    (hrec : AspisR1.MerkleLeafRecovery.recover
      (AspisR1.MerkleRecordedLog.nodes log)
      (AspisR1.MerkleRecordedLog.leaves tag width log) slots root = some data) :
    root ∈ log.map Prod.snd := by
  cases hwalk : AspisR1.MerkleTable.walk
      (AspisR1.MerkleRecordedLog.nodes log) slots root with
  | none => simp [AspisR1.MerkleLeafRecovery.recover, hwalk] at hrec
  | some leaf =>
      obtain ⟨cs, hrootmem⟩ := walk_root_recorded
        (AspisR1.MerkleRecordedLog.nodes log) slots root leaf hnonempty hwalk
      obtain ⟨input, hentry, _⟩ := AspisR1.MerkleRecordedLog.mem_nodes.mp hrootmem
      exact List.mem_map.mpr ⟨(input, root), hentry, rfl⟩

theorem canonical_root_read (tr : List (Addr L × State))
    (tag : AspisR1.Merkle32Path.Byte) (width : Nat) (slots : List (Fin 8))
    (root : Digest) (data : LeafData) (hnonempty : slots ≠ [])
    (hrec : AspisR1.MerkleLeafRecovery.recover
      (AspisR1.MerkleRecordedLog.nodes
        (AspisR1.CanonicalOracleLog.byteLog tr))
      (AspisR1.MerkleRecordedLog.leaves tag width
        (AspisR1.CanonicalOracleLog.byteLog tr)) slots root = some data) :
    ∃ a, (a, root) ∈ tr := by
  have hroot := recover_root_recorded
    (AspisR1.CanonicalOracleLog.byteLog tr) tag width slots root data hnonempty hrec
  change root ∈ ((AspisR1.CanonicalOracleLog.canonicalTrace tr).map
    (fun q => (q.1.toBytes, q.2))).map Prod.snd at hroot
  obtain ⟨entry, hentry, hrootval⟩ := List.mem_map.mp hroot
  obtain ⟨q, hq, hpair⟩ := List.mem_map.mp hentry
  have hqroot : q.2 = root := (congrArg Prod.snd hpair).trans hrootval
  refine ⟨q.1, ?_⟩
  apply List.mem_map.mpr
  refine ⟨q, (AspisR1.CanonicalOracleLog.mem_canonicalTrace.mp hq).1, ?_⟩
  exact Prod.ext rfl hqroot

#print axioms walk_root_recorded
#print axioms recover_root_recorded
#print axioms canonical_root_read

end AspisR1.RecoveredRootRecorded
