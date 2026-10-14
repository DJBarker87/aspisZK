import R1CanonicalLogInputs
import R1CanonicalMerkleProgram

/-! Lift byte-level Merkle collisions to distinct read addresses in the
common finite oracle, then reuse the existing duplex collision event. -/
set_option autoImplicit false
namespace AspisR1.CanonicalMerkleCollision

open FS FS2.Duplex
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf CanonicalByteHash

variable {L : Nat}

theorem read_witness (H : Addr L → State) (pre : List (Addr L × State))
    {slots : List (Fin 8)} (path : Path slots) (leaf : Bytes)
    (hleaf : leaf.length ≤ L) (hnode : 257 ≤ L)
    (hc : CrossTraceCollision (hashBytes H) ((CanonicalOracleLog.byteLog pre).map Prod.fst)
      (fullTrace (hashBytes H) path leaf)) :
    ∃ a b : Addr L, Read pre a ∧
      Read (eval H (CanonicalMerkleProgram.program path leaf)).1 b ∧
      a ≠ b ∧ H a = H b := by
  rcases hc with ⟨left, hleft, right, hright, hne, hhash⟩
  exact ⟨encode left, encode right, CanonicalLogInputs.input_read hleft,
    CanonicalMerkleProgram.read_of_input H path leaf hright,
    CanonicalLogInputs.encode_ne (CanonicalLogInputs.input_length_le hleft)
      (CanonicalMerkleProgram.fullTrace_bounded leaf hleaf hnode path H hright) hne,
    hhash⟩

theorem hits_collision {M Cv : Type} (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre : List (Addr L × State))
    (hpre : ∀ q ∈ pre, q.2 = H q.1)
    {slots : List (Fin 8)} (path : Path slots) (leaf : Bytes)
    (hleaf : leaf.length ≤ L) (hnode : 257 ≤ L)
    (hQ : firstReads emptyTable (pre ++
      (eval H (CanonicalMerkleProgram.program path leaf)).1) ≤ Qtot)
    (hc : CrossTraceCollision (hashBytes H) ((CanonicalOracleLog.byteLog pre).map Prod.fst)
      (fullTrace (hashBytes H) path leaf)) :
    hitsBad (badColl p Qtot) emptyTable
      (pre ++ (eval H (CanonicalMerkleProgram.program path leaf)).1) := by
  classical
  by_contra hfree
  let post := (eval H (CanonicalMerkleProgram.program path leaf)).1
  have hcons : ∀ q ∈ pre ++ post, q.2 = H q.1 := by
    intro q hq
    rcases List.mem_append.mp hq with hp | hs
    · exact hpre q hp
    · exact FS.eval_consistent H (CanonicalMerkleProgram.program path leaf) q hs
  obtain ⟨a, b, ha, hb, hne, hhash⟩ := read_witness H pre path leaf hleaf hnode hc
  have haFull : Read (pre ++ post) a := by
    change a ∈ (pre ++ post).map Prod.fst
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inl ha)
  have hbFull : Read (pre ++ post) b := by
    change b ∈ (pre ++ post).map Prod.fst
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inr hb)
  exact noColl_injective p Qtot H (pre ++ post) hcons hQ hfree a b haFull hbFull hne hhash

#print axioms read_witness
#print axioms hits_collision

end AspisR1.CanonicalMerkleCollision
