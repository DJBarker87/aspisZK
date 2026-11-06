import NJL_TagData
set_option autoImplicit false
namespace AspisR1.NJL_TagPartition
/-- Bounded four-term source chunking. Fuel is derived from the actual
interval length and is not a caller premise or a success witness. -/
def chunks {α : Type} [DecidableEq α] : Nat → List α → List (List α)
 | 0,_=>[]
 | n+1,xs=>if xs=[] then [] else xs.take 4 :: chunks n (xs.drop 4)
theorem flatten {α : Type} [DecidableEq α] (n : Nat) (xs : List α) (small : xs.length≤4*n) :
 (chunks n xs).flatten=xs := by
 induction n generalizing xs with
 | zero => have : xs=[] := List.length_eq_zero.mp (by omega);simp [chunks,this]
 | succ n ih =>
  by_cases h:xs=[]
  · simp [chunks,h]
  · have tail : (xs.drop 4).length≤4*n := by rw [List.length_drop];omega
    simp only [chunks,if_neg h,List.flatten_cons,ih _ tail,List.take_append_drop]
theorem small {α : Type} [DecidableEq α] (n : Nat) (xs : List α) :
 ∀ ys∈chunks n xs,ys.length≤4 := by
 induction n generalizing xs with
 | zero => simp [chunks]
 | succ n ih =>
  by_cases h:xs=[]
  · simp [chunks,h]
  · simp only [chunks,if_neg h,List.mem_cons]
    intro ys hy
    rcases hy with rfl|hy
    · simpa only [List.length_take] using Nat.min_le_left 4 xs.length
    · exact ih _ ys hy
theorem coordinate (c : Fin 30) :
 (chunks 68 (NJL_TagData.indices c)).flatten=NJL_TagData.indices c ∧
 (∀ ys∈chunks 68 (NJL_TagData.indices c),ys.length≤4) := by
 constructor
 · apply flatten
   have := NJL_TagData.interval c
   simp only [NJL_TagData.indices,List.length_ofFn]
   omega
 · exact small _ _
#print axioms flatten
#print axioms small
#print axioms coordinate
end AspisR1.NJL_TagPartition
