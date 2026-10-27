import XRy_ListPowers
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XRy_ArrayRead

theorem read {A : Type} {N : Usize} (a : Array A N) (i : Usize) (hi : i.val<N.val) :
 Array.index_usize a i = ok (a.val[i.val]'(by rw [a.property]; exact hi)) := by
 obtain ⟨x,hx,hv⟩ := WP.spec_imp_exists
   (Array.index_usize_spec a i (by simpa [a.property] using hi))
 exact hx.trans (congrArg ok hv)

theorem mapped {A B : Type} {N : Usize} (f : A → B) (a : Array A N) (i : Usize) (hi : i.val<N.val) :
 Array.index_usize (arr f a) i = ok (f (a.val[i.val]'(by rw [a.property]; exact hi))) := by
 rw [read (arr f a) i hi]
 simp only [arr,List.getElem_map]

theorem usize_small (i : Usize) (hi : i.val<7) : XRn_Join_usize i.val=i := by
 apply UScalar.eq_of_val_eq
 change i.val%(UScalar.cMax .Usize+1)=i.val
 apply Nat.mod_eq_of_lt
 have hmin : 7 ≤ UScalar.cMax .Usize := by scalar_tac
 omega

#print axioms read
#print axioms mapped
#print axioms usize_small
end XRy_ArrayRead
