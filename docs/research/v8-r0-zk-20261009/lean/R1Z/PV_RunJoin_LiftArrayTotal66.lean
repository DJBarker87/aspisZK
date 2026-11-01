import R1Z.PV_RunJoin_LiftArray66
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LiftArrayTotal66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_LiftArray66

def cells (a : Matrix) (i : Nat) : Row :=
  a.val[i%29]'(by rw [a.property];exact Nat.mod_lt _ (by decide))

theorem of_array (a : Matrix) : matrix (cells a)=a := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [matrix,ProverCommitArray49.array,List.length_ofFn,a.property]
  · intro i hi hi'
    have bound : i<29 := by simpa only [matrix,ProverCommitArray49.array,List.length_ofFn,UScalar.ofNatCore_val_eq] using hi
    simp only [matrix,ProverCommitArray49.array,List.getElem_ofFn,cells,Nat.mod_eq_of_lt bound]

theorem congr (p q : Nat → Row) (eq : ∀ i,i<29 → p i=q i) : matrix p=matrix q := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [matrix,ProverCommitArray49.array,List.length_ofFn]
  · intro i hi hi'
    simp only [matrix,ProverCommitArray49.array,List.getElem_ofFn]
    apply eq
    simpa only [matrix,ProverCommitArray49.array,List.length_ofFn,UScalar.ofNatCore_val_eq] using hi

#print axioms cells
#print axioms of_array
#print axioms congr
end R1Z.PV_RunJoin_LiftArrayTotal66
