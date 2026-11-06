import MultiproofConePadding

set_option autoImplicit false
namespace NKB_PaddingFrame
open AspisV8R19.DuplexFrames AspisR1

/-- The real fixed-slot geometry rules out chunks_exact's ignored remainder. -/
theorem aligned (bytes : Bytes) (cap count : Nat)
    (width : bytes.length=32*cap) (fits : count≤cap) :
 (bytes.drop (32*count)).length=8*(4*(cap-count)) ∧
 (bytes.drop (32*count)).length%8=0 := by
 simp only [List.length_drop,width]
 omega

/-- No assumed zero suffix: the exact word scan establishes it, on the SAME
slot and count. This frame law is shared by each separately checked occurrence. -/
theorem zero_suffix (bytes : Bytes) (cap count : Nat)
    (width : bytes.length=32*cap) (fits : count≤cap)
    (scanned : MultiproofConePadding.scan (4*(cap-count)) (bytes.drop (32*count))=true) :
 bytes=bytes.take (32*count)++List.replicate (32*(cap-count)) 0 := by
 have zero := (MultiproofConePadding.padding cap count bytes width fits).mp scanned
 calc
  bytes=bytes.take (32*count)++bytes.drop (32*count) := (List.take_append_drop _ _).symm
  _=bytes.take (32*count)++List.replicate (32*(cap-count)) 0 := by rw [zero]

/-- A nonzero padding byte forces rejection; no hash or verification call is
needed to witness this branch of a correctly counted terminal. -/
theorem nonzero_rejects (bytes : Bytes) (cap count : Nat)
    (width : bytes.length=32*cap) (fits : count≤cap)
    (nonzero : ∃ b∈bytes.drop (32*count),b≠0) :
 MultiproofConePadding.scan (4*(cap-count)) (bytes.drop (32*count))=false := by
 cases h : MultiproofConePadding.scan (4*(cap-count)) (bytes.drop (32*count)) with
 | false => rfl
 | true =>
   have eq := (MultiproofConePadding.padding cap count bytes width fits).mp h
   obtain ⟨b,member,different⟩ := nonzero
   rw [eq] at member
   exact (different (List.eq_of_mem_replicate member)).elim

#print axioms aligned
#print axioms zero_suffix
#print axioms nonzero_rejects
end NKB_PaddingFrame
