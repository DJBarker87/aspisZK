import BinMerkleRecordedLog
import BinMerkleTraceInputs

/-! Mirrors `MerkleLogRecovery.lean`; see design/BIN-COMMITMENT-MODEL-20261019.md for line pins.
 Recover from a literal, consistent prior query log. Failure is either a
cross-trace collision or an opening input absent from that prior log whose
hash hits the root or a recorded child. This is deterministic; the prior log
must still be identified with an actual commitment-time execution prefix. -/
set_option autoImplicit false
namespace AspisR1.BinMerkleLogRecovery

open BinMerkle32Path BinMerkle32Leaf BinMerkleTable BinMerkleLeafRecovery BinMerkleRecordedLog

abbrev Byte := BinMerkle32Path.Byte

theorem nodeInputs_subset (log : Log) :
    BinMerkleRecovery.nodeInputs (nodes log) ⊆ log.map Prod.fst := by
  intro input hin
  obtain ⟨⟨cs, digest⟩, hentry, rfl⟩ := List.mem_map.mp hin
  obtain ⟨recorded, hrecorded, hparse⟩ := mem_nodes.mp hentry
  have heq := BinMerkleNodeCodec.parse_sound hparse
  exact List.mem_map.mpr ⟨(recorded, digest), hrecorded, heq.symm⟩

theorem leafInputs_subset (tag : Byte) (width : Nat) (log : Log) :
    leafInputs tag (leaves tag width log) ⊆ log.map Prod.fst := by
  intro input hin
  obtain ⟨⟨data, digest⟩, hentry, rfl⟩ := List.mem_map.mp hin
  obtain ⟨recorded, hrecorded, hparse⟩ := mem_leaves.mp hentry
  have heq := (BinMerkleLeafCodec.parse_sound tag width recorded data hparse).2.2
  exact List.mem_map.mpr ⟨(recorded, digest), hrecorded, heq.symm⟩

def AbsentTargetHit (hash : List Byte → Digest) (log : Log)
    (root : Digest) (trace : List (List Byte)) : Prop :=
  ∃ input ∈ trace, input ∉ log.map Prod.fst ∧ hash input ∈ targets (nodes log) root

theorem recover_or_bad (hash : List Byte → Digest) (log : Log)
    (hlog : BinMerkleRecordedLog.Consistent hash log) (tag : Byte) (width : Nat)
    (packed salt : List Byte) (hw : packed.length = width) (hs : salt.length = 32)
    {slots : List (Fin 2)} (path : Path slots) (root : Digest)
    (hroot : root = foldPath hash path (hash (leafInput tag packed salt))) :
    recover (nodes log) (leaves tag width log) slots root = some (packed, salt) ∨
      CrossTraceCollision hash (log.map Prod.fst)
        (fullTrace hash path (leafInput tag packed salt)) ∨
      AbsentTargetHit hash log root (fullTrace hash path (leafInput tag packed salt)) := by
  have hc := BinMerkleLeafRecovery.recover_or_bad hash (nodes log) (leaves tag width log)
    tag packed salt (nodes_consistent hash log hlog)
    (leaves_consistent hash tag width log hlog) width (leaves_width tag width log)
    hw (leafInput tag packed salt) rfl path root hroot
  rcases hc with hrecovered | hcollision | hnode | hleaf
  · exact Or.inl hrecovered
  · rcases hcollision with ⟨left, hleft, right, hright, hne, heq⟩
    refine Or.inr (Or.inl ⟨left, ?_, right, hright, hne, heq⟩)
    rcases List.mem_append.mp hleft with hn | hl
    · exact nodeInputs_subset log hn
    · exact leafInputs_subset tag width log hl
  · rcases hnode with ⟨input, hin, htarget, hmissing⟩
    obtain ⟨children, hshape⟩ := BinMerkleTraceInputs.inputTrace_node_shape hash path _ hin
    refine Or.inr (Or.inr ⟨input, List.mem_cons_of_mem _ hin, ?_, htarget⟩)
    rw [hshape] at hmissing ⊢
    exact missing_node_absent hash log hlog children hmissing
  · rcases hleaf with ⟨htarget, hmissing⟩
    exact Or.inr (Or.inr ⟨leafInput tag packed salt, by simp [fullTrace],
      missing_leaf_absent hash tag width log hlog packed salt hw hs hmissing, htarget⟩)


#print axioms nodeInputs_subset
#print axioms leafInputs_subset
#print axioms recover_or_bad

end AspisR1.BinMerkleLogRecovery
