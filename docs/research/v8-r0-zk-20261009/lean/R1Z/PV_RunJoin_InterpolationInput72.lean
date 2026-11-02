import R1Z.PV_RunJoin_MergeArray35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_InterpolationInput72
open Aeneas Aeneas.Std ProverRwFull
abbrev Q := aspis_core.field.QM31

def cells (a : Array Q 28#usize) (i : Nat) : Q :=
  a.val[i%28]'(by rw [a.property];exact Nat.mod_lt _ (by decide))

theorem complete (a : Array Q 28#usize) : PV_RunJoin_MergeArray35.array (cells a)=a := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [PV_RunJoin_MergeArray35.array,ProverCommitArray49.array,List.length_ofFn,a.property]
  · intro i hi hi'
    have bound : i<28 := by
      simpa only [PV_RunJoin_MergeArray35.array,ProverCommitArray49.array,List.length_ofFn,UScalar.ofNatCore_val_eq] using hi
    simp only [PV_RunJoin_MergeArray35.array,ProverCommitArray49.array,List.getElem_ofFn,cells,Nat.mod_eq_of_lt bound]

#print axioms cells
#print axioms complete
end R1Z.PV_RunJoin_InterpolationInput72
