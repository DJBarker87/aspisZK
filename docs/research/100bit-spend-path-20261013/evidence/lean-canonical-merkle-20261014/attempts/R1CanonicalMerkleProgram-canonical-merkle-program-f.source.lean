import R1CanonicalByteHash
import R1MerkleProgram
import R1MerkleTraceInputs
import FS2.DuplexTrace

/-! Canonical-address renaming of the generic Merkle32 path program. -/
set_option autoImplicit false
namespace AspisR1.CanonicalMerkleProgram

open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.Merkle32Path AspisR1.Merkle32Leaf

def program {L : Nat} {slots : List (Fin 8)}
    (path : Path slots) (leaf : Bytes) : Program (Addr L) State State :=
  AspisV8R19.OracleProgramOps.rename CanonicalByteHash.encode
    (MerkleProgram.leafProgram path leaf)

theorem eval_program {L : Nat} (H : Addr L → State)
    {slots : List (Fin 8)} (path : Path slots) (leaf : Bytes) :
    eval H (program path leaf) =
      ((fullTrace (CanonicalByteHash.hashBytes H) path leaf).map
        (fun input => (CanonicalByteHash.encode input,
          CanonicalByteHash.hashBytes H input)),
        foldPath (CanonicalByteHash.hashBytes H) path
          (CanonicalByteHash.hashBytes H leaf)) := by
  rw [program, eval_rename, MerkleProgram.eval_leafProgram]
  unfold AspisV8R19.OracleProgramOps.mapView
  change
    ((fullTrace (fun input => H (CanonicalByteHash.encode input)) path leaf).map
      (fun input => (CanonicalByteHash.encode input, H (CanonicalByteHash.encode input))),
      foldPath (fun input => H (CanonicalByteHash.encode input)) path
        (H (CanonicalByteHash.encode leaf))) =
    ((fullTrace (fun input => H (CanonicalByteHash.encode input)) path leaf).map
      (fun input => (CanonicalByteHash.encode input, H (CanonicalByteHash.encode input))),
      foldPath (fun input => H (CanonicalByteHash.encode input)) path
        (H (CanonicalByteHash.encode leaf)))
  rfl

theorem read_of_input {L : Nat} (H : Addr L → State)
    {slots : List (Fin 8)} (path : Path slots) (leaf : Bytes)
    {input : Bytes}
    (hin : input ∈ fullTrace (CanonicalByteHash.hashBytes H) path leaf) :
    Read (eval H (program path leaf)).1 (CanonicalByteHash.encode input) := by
  rw [eval_program]
  change CanonicalByteHash.encode input ∈
    ((fullTrace (CanonicalByteHash.hashBytes H) path leaf).map
      (fun input => (CanonicalByteHash.encode input,
        CanonicalByteHash.hashBytes H input))).map Prod.fst
  rw [List.map_map]
  exact List.mem_map.mpr ⟨input, hin, rfl⟩

theorem fullTrace_bounded {L : Nat} (leaf : Bytes) (hleaf : leaf.length ≤ L)
    (hnode : 257 ≤ L) {slots : List (Fin 8)}
    (path : Path slots) (H : Addr L → State) {input : Bytes}
    (hin : input ∈ fullTrace (CanonicalByteHash.hashBytes H) path leaf) :
    input.length ≤ L := by
  unfold fullTrace at hin
  simp only [List.mem_cons] at hin
  rcases hin with h | h
  · cases h
    exact hleaf
  · obtain ⟨children, rfl⟩ := MerkleTraceInputs.inputTrace_node_shape
      (CanonicalByteHash.hashBytes H) path _ h
    rw [Merkle32Path.nodeInput_length]
    exact hnode
theorem reads_canonical {L : Nat} (H : Addr L → State)
    {slots : List (Fin 8)} (path : Path slots) (leaf : Bytes)
    (q : Addr L × State) (hq : q ∈ (eval H (program path leaf)).1) :
    CanonicalByteAddress.Canonical q.1 := by
  rw [eval_program] at hq
  rcases List.mem_map.mp hq with ⟨input, hin, heq⟩
  cases heq
  exact CanonicalByteHash.encode_canonical input

#print axioms eval_program
#print axioms read_of_input
#print axioms fullTrace_bounded
#print axioms reads_canonical

end AspisR1.CanonicalMerkleProgram
