import R1Z.ProverCommitWideArray48
/-! Generic list padding, before any 256/1024 array or tower instantiation. -/
set_option autoImplicit false
namespace R1Z.ProverCommitArrayPad49

theorem pad_list {A : Type} (m n : Nat) (f : Nat → A) (z : A) :
    List.ofFn (fun i : Fin m => f i.val)++List.replicate n z=
      List.ofFn (fun i : Fin (m+n) => if i.val<m then f i.val else z) := by
  apply List.ext_getElem
  · simp only [List.length_append,List.length_ofFn,List.length_replicate]
  · intro i hi hj
    by_cases h : i<m
    · rw [List.getElem_append_left (by rw [List.length_ofFn];exact h)]
      simp only [List.getElem_ofFn,if_pos h]
    · rw [List.getElem_append_right (by rw [List.length_ofFn];omega)]
      simp only [List.getElem_replicate,List.getElem_ofFn,if_neg h]

#print axioms pad_list
end R1Z.ProverCommitArrayPad49
