import R1Z.ProverCommitMix48
/-! Symbolic array update/replicate image, independent of any concrete table. -/
set_option autoImplicit false
namespace R1Z.ProverCommitWideArray48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48

theorem update (n : Usize) (xs : Nat → Raw) (i : Usize) (hi : i.val<n.val) (x : Raw) :
    Array.update (sourceArray n xs) i (source x) =
      ok (sourceArray n (Function.update xs i.val x)) := by
  have hidx : i.val<(sourceArray n xs).val.length := by simp only [sourceArray,List.length_ofFn];exact hi
  obtain ⟨out,hout,hset⟩ := WP.spec_imp_exists
    (Array.update_spec (sourceArray n xs) i (source x) hidx)
  rw [hout]
  apply congrArg Result.ok
  rw [hset]
  apply Subtype.ext
  change (sourceArray n xs).val.set i.val (source x) =
    (sourceArray n (Function.update xs i.val x)).val
  apply List.ext_getElem
  · simp only [List.length_set,sourceArray,List.length_ofFn]
  · intro k hk1 hk2
    simp only [sourceArray,List.getElem_set,List.getElem_ofFn]
    by_cases h : k=i.val
    · subst k
      simp only [Function.update_self,if_true]
    · simp only [Ne.symm h,if_false,Function.update_of_ne h]


#print axioms update
end R1Z.ProverCommitWideArray48
