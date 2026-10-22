import R1Z.ProverCommitNativeQ48
import R1Z.ProverCommitArrayIndex25
/-! Symbolic canonical-QM31 array image for interpolation accumulation. -/
set_option autoImplicit false
namespace R1Z.ProverCommitQArray48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47

def array (size : Usize) (xs : Nat → Old.Q) : Aeneas.Std.Array field.QM31 size :=
  ⟨List.ofFn (fun i : Fin size.val => ProverCommitNativeQ48.source (xs i.val)),by simp only [List.length_ofFn]⟩

theorem index (size : Usize) (xs : Nat → Old.Q) (i : Usize) (hi : i.val < size.val) :
    Aeneas.Std.Array.index_usize (array size xs) i=ok (ProverCommitNativeQ48.source (xs i.val)) := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ hi]
  simp only [array,List.getElem_ofFn]

theorem update (size : Usize) (xs : Nat → Old.Q) (i : Usize) (hi : i.val < size.val) (z : Old.Q) :
    Aeneas.Std.Array.update (array size xs) i (ProverCommitNativeQ48.source z)=
      ok (array size (Function.update xs i.val z)) := by
  have hidx : i.val < (array size xs).val.length := by simp only [array,List.length_ofFn];exact hi
  obtain ⟨out,hout,hset⟩ := WP.spec_imp_exists
    (Aeneas.Std.Array.update_spec (array size xs) i (ProverCommitNativeQ48.source z) hidx)
  rw [hout]
  apply congrArg Result.ok
  rw [hset]
  apply Subtype.ext
  change (array size xs).val.set i.val (ProverCommitNativeQ48.source z)=
    (array size (Function.update xs i.val z)).val
  apply List.ext_getElem
  · simp only [List.length_set,array,List.length_ofFn]
  · intro k hk1 hk2
    simp only [array,List.getElem_set,List.getElem_ofFn]
    by_cases h : k=i.val
    · subst k;simp only [Function.update_self,if_true]
    · simp only [Ne.symm h,if_false,Function.update_of_ne h]

theorem source_zero : field.QM31.ZERO=ProverCommitNativeQ48.source zero := by
  simp only [field.QM31.ZERO,ProverCommitNativeQ48.source,ProverCommitRelease47.convQ,
    ProverCommitRelease47.convC,fromQ,fromC,zero]

theorem repeat_zero (size : Usize) : Aeneas.Std.Array.repeat size field.QM31.ZERO=array size (fun _ => zero) := by
  rw [source_zero]
  apply Subtype.ext
  simp only [Aeneas.Std.Array.repeat,array,List.ofFn_const]

#print axioms index
#print axioms update
#print axioms source_zero
#print axioms repeat_zero
end R1Z.ProverCommitQArray48
