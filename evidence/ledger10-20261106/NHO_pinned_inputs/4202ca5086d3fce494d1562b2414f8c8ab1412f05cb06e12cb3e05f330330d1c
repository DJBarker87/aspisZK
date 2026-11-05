import NGU_Carriers
open Aeneas Aeneas.Std Result NGU_Carriers
set_option autoImplicit false
namespace NGU_ArrayRead
theorem read {A : Type} {N : Usize} (a : Array A N) (i : Usize) (hi : i.val<N.val) :
 Array.index_usize a i = ok (a.val[i.val]'(by rw [a.property]; exact hi)) := by
 obtain ⟨x,hx,hv⟩ := WP.spec_imp_exists
   (Array.index_usize_spec a i (by simpa [a.property] using hi))
 exact hx.trans (congrArg ok hv)

theorem mapped {A B : Type} {N : Usize} (f : A → B) (a : Array A N) (i : Usize) (hi : i.val<N.val) :
 Array.index_usize (arr f a) i = ok (f (a.val[i.val]'(by rw [a.property]; exact hi))) := by
 rw [read (arr f a) i hi]
 simp only [arr,List.getElem_map]

#print axioms read
#print axioms mapped
end NGU_ArrayRead
