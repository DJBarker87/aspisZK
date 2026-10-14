import R1MerkleRecordedLog
import R1MerkleChildTargets

/-! Relate child targets in the parsed byte log to the eight already checked
address parsers. The supplied commitment root remains a separate case. -/
set_option autoImplicit false
namespace AspisR1.MerkleRecordedTargets

open FS2.Duplex
open AspisV8R19.SourceDuplexStep
open Merkle32Path MerkleTable MerkleRecordedLog

variable {L : Nat}

def byteLog (tr : List (Addr L × State)) : Log :=
  tr.map fun q => (q.1.toBytes, q.2)

theorem target_cases (tr : List (Addr L × State)) (root target : State)
    (h : target ∈ targets (nodes (byteLog tr)) root) :
    target = root ∨ ∃ b, Read tr b ∧ ∃ j : Fin 8,
      MerkleChildTargets.pred j b = some target := by
  rcases List.mem_cons.mp h with heq | hchild
  · exact Or.inl heq
  · obtain ⟨⟨children, digest⟩, hentry, hslot⟩ := List.mem_flatMap.mp hchild
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hslot
    obtain ⟨input, hinput, hp⟩ := mem_nodes.mp hentry
    obtain ⟨⟨b, output⟩, hb, heq⟩ := List.mem_map.mp hinput
    have hbytes : b.toBytes = input := congrArg Prod.fst heq
    right
    refine ⟨b, List.mem_map.mpr ⟨(b, output), hb, rfl⟩, j, ?_⟩
    simp only [MerkleChildTargets.pred, hbytes, hp, Option.map_some]
    exact congrArg some hj

theorem absent_bytes_not_read (tr : List (Addr L × State)) (a : Addr L)
    (h : a.toBytes ∉ (byteLog tr).map Prod.fst) : ¬ Read tr a := by
  intro ha
  obtain ⟨⟨b, output⟩, hb, heq⟩ := List.mem_map.mp ha
  dsimp at heq
  subst b
  exact h (List.mem_map.mpr ⟨(a.toBytes, output),
    List.mem_map.mpr ⟨(a, output), hb, rfl⟩, rfl⟩)

#print axioms target_cases
#print axioms absent_bytes_not_read

end AspisR1.MerkleRecordedTargets
