import LPq_OutputDomains
set_option autoImplicit false
namespace AspisR1.LPq_ArrayPorts
open Aeneas Aeneas.Std Result LPi_FieldValues XRo_Join_Carriers

theorem update {A : Type} {N : Usize} (a : Array A N) (i : Usize) (v : A)
    (hi : i.val<N.val) : Array.update a i v=ok (a.set i v) := by
  simp only [Array.update,Array.index_mut_usize]
  have h : i.val<a.val.length := by rw [a.property]; exact hi
  simp only [if_pos h,bind_tc_ok]

theorem mapped {A B : Type} {N : Usize} (f : A → B) (a : Array A N)
    (i : Usize) (v : A) (hi : i.val<N.val) :
    Array.update (arr f a) i (f v)=ok (arr f (a.set i v)) := by
  rw [update _ _ _ hi,XRy_ArrayMap.set]

theorem canonical_set (a : LPq_WeightedStep.Seven) (i : Usize) (v : NE)
    (ha : LPq_WeightedStep.canonical a) (hv : canonE v) :
    LPq_WeightedStep.canonical (a.set i v) := by
  intro z hz
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hz
  simp only [Array.set,List.getElem_set] at *
  split
  · exact hv
  · exact ha _ (List.getElem_mem _)

#print axioms update
#print axioms mapped
#print axioms canonical_set
end AspisR1.LPq_ArrayPorts
