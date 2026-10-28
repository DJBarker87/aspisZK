import R1Z.ProverCommitArray49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ArrayEntries41
open Aeneas Aeneas.Std
variable {A : Type}

def entries {size : Usize} (xs : Array A size) (fallback : A) (i : Nat) : A :=
  xs.val[i]?.getD fallback

theorem rebuild {size : Usize} (xs : Array A size) (fallback : A) :
    ProverCommitArray49.array size (entries xs fallback)=xs := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [ProverCommitArray49.array,List.length_ofFn,xs.property]
  · intro i hleft hright
    simp only [ProverCommitArray49.array,List.getElem_ofFn,entries]
    rw [List.getElem?_eq_getElem hright]
    rfl
#print axioms rebuild
end R1Z.PV_RunJoin_ArrayEntries41
