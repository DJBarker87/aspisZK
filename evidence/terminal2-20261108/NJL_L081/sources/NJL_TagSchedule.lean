import NJL_TagPartition
set_option autoImplicit false
namespace AspisR1.NJL_TagSchedule
/-- Native min/guard/next arithmetic for one arbitrary chunk. This is the
K029/K030 cut in natural carriers; the small bound establishes usize safety. -/
theorem chunk (start stop : Nat) (entered : start<stop) (bounded : stop≤272) :
 let next := min (start+4) stop
 start<next ∧ next≤stop ∧ next≤272 ∧ next-start≤4 ∧
 next=start+min 4 (stop-start) := by
 dsimp
 omega
/-- The remaining term list, not a fresh independent array, determines
EVERY source chunk. A nonempty head consumes take4, followed by drop4. -/
inductive Schedule {α : Type} : List α → List (List α) → Prop
 | nil : Schedule [] []
 | cons (xs : List α) (rest : List (List α)) (entered : xs≠[])
   (tail : Schedule (xs.drop 4) rest) : Schedule xs (xs.take 4::rest)
theorem source {α : Type} [DecidableEq α] (n : Nat) (xs : List α) (small : xs.length≤4*n) :
 Schedule xs (NJL_TagPartition.chunks n xs) := by
 induction n generalizing xs with
 | zero =>
  have h : xs=[] := (by
    cases xs with
    | nil => rfl
    | cons x rest => simp only [List.length_cons] at small;omega)
  subst xs;exact .nil
 | succ n ih =>
  by_cases h:xs=[]
  · subst xs;simp only [NJL_TagPartition.chunks,if_pos rfl];exact .nil
  · rw [NJL_TagPartition.chunks,if_neg h]
    exact .cons xs _ h (ih _ (by rw [List.length_drop];omega))
theorem coordinate (c : Fin 30) :
 Schedule (NJL_TagData.indices c) (NJL_TagPartition.chunks 68 (NJL_TagData.indices c)) ∧
 (NJL_TagData.indices c).map Fin.val=List.range' (NJL_TagData.first c) (NJL_TagData.last c-NJL_TagData.first c) := by
 refine ⟨source _ _ ?_,NJL_TagData.range_values c⟩
 have := NJL_TagData.interval c
 simp only [NJL_TagData.indices,List.length_ofFn]
 omega
#print axioms chunk
#print axioms source
#print axioms coordinate
end AspisR1.NJL_TagSchedule
