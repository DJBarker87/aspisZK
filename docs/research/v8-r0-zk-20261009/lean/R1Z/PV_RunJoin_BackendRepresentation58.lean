import R1Z.PV_RunJoin_BackendMatrix58
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendRepresentation58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_BackendMatrix58

theorem matrix_congr (p q : Nat → Nat → W)
    (h : ∀ l,l<29 → ∀ j,j<1024 → p l j=q l j) : matrix p=matrix q := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [matrix,List.length_ofFn]
  · intro l hl hl'
    simp only [matrix,List.getElem_ofFn]
    apply Subtype.ext
    apply List.ext_getElem
    · simp only [ProverCommitArray49.array,List.length_ofFn]
    · intro j hj hj'
      simp only [ProverCommitArray49.array,List.getElem_ofFn]
      apply h
      · simpa only [matrix,List.length_ofFn] using hl
      · simpa only [ProverCommitArray49.array,List.length_ofFn] using hj

def cells (v : alloc.vec.Vec Column) (h : v.length=29) (l j : Nat) : W :=
  let column := v.val[l%29]'(by change l%29<v.length;rw [h];exact Nat.mod_lt _ (by decide))
  column.val[j%1024]'(by rw [column.property];exact Nat.mod_lt _ (by decide))

theorem of_vec (v : alloc.vec.Vec Column) (h : v.length=29) : matrix (cells v h)=v := by
  apply Subtype.ext
  apply List.ext_getElem
  · simpa only [matrix,List.length_ofFn] using h.symm
  · intro l hl hl'
    simp only [matrix,List.getElem_ofFn]
    apply Subtype.ext
    apply List.ext_getElem
    · simp only [ProverCommitArray49.array,List.length_ofFn,Array.length]
    · intro j hj hj'
      have bl : l<29 := by simpa only [matrix,List.length_ofFn] using hl
      have bj : j<1024 := by simpa only [ProverCommitArray49.array,List.length_ofFn] using hj
      simp only [ProverCommitArray49.array,List.getElem_ofFn,cells,
        Nat.mod_eq_of_lt bl,Nat.mod_eq_of_lt bj]

#print axioms matrix_congr
#print axioms of_vec
end R1Z.PV_RunJoin_BackendRepresentation58
