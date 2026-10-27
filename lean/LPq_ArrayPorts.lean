import LPq_OutputDomains
set_option autoImplicit false
namespace AspisR1.LPq_ArrayPorts
open Aeneas Aeneas.Std Result LPi_FieldValues XRo_Join_Carriers

theorem update {A : Type} {N : Usize} (a : Array A N) (i : Usize) (v : A)
    (hi : i.val<N.val) : Array.update a i v=ok (a.set i v) := by
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists (Array.update_spec a i v (by simpa only [Array.length,a.property] using hi))
  exact call.trans (congrArg ok value)

theorem mapped {A B : Type} {N : Usize} (f : A → B) (a : Array A N)
    (i : Usize) (v : A) (hi : i.val<N.val) :
    Array.update (arr f a) i (f v)=ok (arr f (a.set i v)) := by
  rw [update _ _ _ hi,XRy_ArrayMap.set]

theorem canonical_set (a : LPq_WeightedStep.Seven) (i : Usize) (v : NE)
    (ha : LPq_WeightedStep.canonical a) (hv : canonE v) :
    LPq_WeightedStep.canonical (a.set i v) := by
  change ∀ z ∈ a.val.set i.val v, canonE z
  intro z hz
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hz
  rw [List.getElem_set]
  split
  · exact hv
  · exact ha _ (List.getElem_mem _)

#print axioms update
#print axioms mapped
#print axioms canonical_set
end AspisR1.LPq_ArrayPorts
