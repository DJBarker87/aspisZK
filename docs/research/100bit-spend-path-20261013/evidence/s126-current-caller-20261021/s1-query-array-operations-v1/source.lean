import Aeneas.Std
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS1QueryArrayOperations

/-- TOTAL in the extracted Std model, including the exact returned setter.
Native Std/allocator interpretation is not asserted by these local laws. -/
theorem index_total {A : Type} {n : Usize} (a : Array A n) (i : Usize)
    (bound : i.val<n.val) :
    Array.index_usize a i=ok (a.val[i.val]'(by simpa [a.property] using bound)) := by
  have hi : i.val<a.length := by simpa [a.property] using bound
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hi)
  rw [value] at call
  exact call

theorem update_total {A : Type} {n : Usize} (a : Array A n) (i : Usize) (value : A)
    (bound : i.val<n.val) : Array.update a i value=ok (a.set i value) := by
  have hi : i.val<a.length := by simpa [a.property] using bound
  obtain ⟨out,call,valueEq⟩ := WP.spec_imp_exists (Array.update_spec a i value hi)
  have same : out=a.set i value := by
    apply Subtype.ext
    exact valueEq.trans (Array.set_val_eq a i value).symm
  simpa only [same] using call

theorem index_mut_total {A : Type} {n : Usize} (a : Array A n) (i : Usize)
    (bound : i.val<n.val) :
    Array.index_mut_usize a i=ok
      (a.val[i.val]'(by simpa [a.property] using bound),fun value => a.set i value) := by
  have hi : i.val<a.length := by simpa [a.property] using bound
  obtain ⟨out,call,valueEq,setterEq⟩ := WP.spec_imp_exists (Array.index_mut_usize_spec a i hi)
  rcases out with ⟨old,back⟩
  simp only at valueEq setterEq
  rw [valueEq,setterEq] at call
  exact call

#print axioms index_total
#print axioms update_total
#print axioms index_mut_total
end AspisS1QueryArrayOperations
