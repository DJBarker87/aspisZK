import PAln_RowBounds
set_option autoImplicit false
namespace AspisR1.PAln_SubSlice
open AspisV8R19.DuplexFrames OraclePortCompactDraft

theorem nested (b : Bytes) (start size offset count : Nat) (h : offset+count≤size) :
    slice (slice b start size) offset count=slice b (start+offset) count := by
  simp only [slice,List.drop_take,List.drop_drop,List.take_take]
  congr 1
  omega

theorem canonical_slice (b : Bytes) (offset count : Nat)
    (checked : canonical b) (aligned : offset%4=0) (size : count%4=0)
    (bound : offset+count≤b.length) : canonical (slice b offset count) := by
  have tail := ((MultiproofConeCanonicalAppend.canonical_take_drop b offset aligned (by omega)).mp checked).2
  have h := (MultiproofConeCanonicalAppend.canonical_take_drop (b.drop offset) count size
    (by simp only [List.length_drop];omega)).mp tail
  exact h.1

#print axioms nested
#print axioms canonical_slice
end AspisR1.PAln_SubSlice
