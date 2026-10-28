import NBR_OpeningPayload
set_option autoImplicit false
namespace AspisR1.NBR_AppendInduction

/-- The indexed native source read is the head consumed by the existing
append induction, with the SAME source list and successor position. -/
theorem step {α : Type} (dst src : List α) (i : Nat) (bound : i<src.length) :
    KMX_CopyMeaning.appendLoop dst (src.drop i)=
      KMX_CopyMeaning.appendLoop (dst++[src[i]]) (src.drop (i+1)) := by
  rw [List.drop_eq_getElem_cons bound]
  rfl

theorem prefix_step {α : Type} (dst src : List α) (i : Nat) (bound : i<src.length) :
    (dst++src.take i)++[src[i]]=dst++src.take (i+1) := by
  rw [List.take_succ_eq_append_getElem bound,List.append_assoc]

/-- Every reached push has spare capacity, established from the complete
source length rather than an assumed per-iteration invariant. -/
theorem capacity {α : Type} (dst src : List α) (i : Nat)
    (size : dst.length+src.length≤256) (bound : i<src.length) :
    (dst++src.take i).length=dst.length+i ∧ (dst++src.take i).length<256 := by
  have prefixLen : (src.take i).length=i := List.length_take_of_le (by omega)
  have length : (dst++src.take i).length=dst.length+i := by
    simp only [List.length_append,prefixLen]
  refine ⟨length,?_⟩
  rw [length]
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left bound dst.length) size

#print axioms step
#print axioms prefix_step
#print axioms capacity
end AspisR1.NBR_AppendInduction
