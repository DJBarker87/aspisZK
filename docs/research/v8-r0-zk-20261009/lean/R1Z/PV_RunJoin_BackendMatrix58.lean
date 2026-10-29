import R1Z.PV_RunJoin_BackendStoreSafe55
import R1Z.ProverCommitArray49
import R1Z.PV_RunJoin_Vector44
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendMatrix58
open Aeneas Aeneas.Std Result ProverRwFull
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Column := Array W 1024#usize

def matrix (p : Nat → Nat → W) : alloc.vec.Vec Column :=
  ⟨List.ofFn (fun l : Fin 29 => ProverCommitArray49.array 1024#usize (p l.val)),by
    simp only [List.length_ofFn]; scalar_tac⟩

theorem length (p : Nat → Nat → W) : (matrix p).length=29 := by
  change (List.ofFn _).length=29
  rw [List.length_ofFn]

theorem deref (p : Nat → Nat → W) :
    alloc.vec.Vec.deref (matrix p)=Array.to_slice
      (ProverCommitArray49.array 29#usize (fun l => ProverCommitArray49.array 1024#usize (p l))) := by
  rfl

theorem set (p : Nat → Nat → W) (lane : Usize) (hl : lane.val<29) (values : Nat → W) :
    alloc.vec.Vec.set (matrix p) lane (ProverCommitArray49.array 1024#usize values)=
      matrix (Function.update p lane.val values) := by
  apply Subtype.ext
  change (List.ofFn (fun l : Fin 29 => ProverCommitArray49.array 1024#usize (p l.val))).set lane.val
    (ProverCommitArray49.array 1024#usize values)=_
  apply List.ext_getElem
  · simp only [matrix,List.length_set,List.length_ofFn]
  · intro j hj hj'
    simp only [matrix,List.getElem_set,List.getElem_ofFn]
    by_cases he : j=lane.val
    · subst j
      simp only [Function.update_self,if_true]
    · simp only [he,Ne.symm he,if_false,Function.update_of_ne he]

#print axioms length
#print axioms deref
#print axioms set
end R1Z.PV_RunJoin_BackendMatrix58
