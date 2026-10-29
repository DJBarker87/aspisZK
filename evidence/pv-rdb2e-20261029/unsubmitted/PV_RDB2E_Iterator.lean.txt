import R1Z.PV_RDB2D_SamplerCore
/-! Non-ZST iterator offset projection. The raw-pointer/provenance-to-offset
refinement is a separate native obligation; this file does not assume it. -/
namespace R1Z.PV_RDB2E_Iterator
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Words := Array U32 8#usize
structure Cursor where
  front : Usize
  back : Usize
structure Handle where
  index : Usize

def restore (current : Words) (h : Handle) (value : U32) : Result Words :=
  Array.update current h.index value

def next (current : Words) (c : Cursor) : Result (Option (U32 × Handle × Cursor)) := do
  if c.front < c.back then
    let word ← Array.index_usize current c.front
    let front ← lift (Usize.wrapping_add c.front 1#usize)
    ok (some (word,⟨c.front⟩,⟨front,c.back⟩))
  else ok none

def nextBack (current : Words) (c : Cursor) : Result (Option (U32 × Handle × Cursor)) := do
  if c.front < c.back then
    let back ← lift (Usize.wrapping_sub c.back 1#usize)
    let word ← Array.index_usize current back
    ok (some (word,⟨back⟩,⟨c.front,back⟩))
  else ok none

theorem back_source (q : Words) (j : Usize) (active : 0#usize < j) :
    nextBack q ⟨0#usize,j⟩ =
      (do let i ← lift (Usize.wrapping_sub j 1#usize)
          let word ← Array.index_usize q i
          ok (some (word,⟨i⟩,⟨0#usize,i⟩))) := by
  simp only [nextBack,active,if_true]

theorem forward_source (q : Words) (i : Usize) (active : i < 8#usize) :
    next q ⟨i,8#usize⟩ =
      (do let word ← Array.index_usize q i
          let j ← lift (Usize.wrapping_add i 1#usize)
          ok (some (word,⟨i⟩,⟨j,8#usize⟩))) := by
  simp only [next,active,if_true]

theorem current_store (original current : Words) (h : Handle) (value : U32) :
    (fun (_ : Words) => restore current h value) original=Array.update current h.index value := rfl

theorem exhausted (q : Words) (i : Usize) :
    next q ⟨i,i⟩=ok none ∧ nextBack q ⟨i,i⟩=ok none := by
  simp only [next,nextBack,lt_self_iff_false,if_false,and_self]

#print axioms back_source
#print axioms forward_source
#print axioms current_store
#print axioms exhausted
end R1Z.PV_RDB2E_Iterator
