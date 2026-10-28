import NCV_ArrayFrame
set_option autoImplicit false
namespace NCV_ArrayRead
open Aeneas Aeneas.Std Result

theorem read {A : Type} [Inhabited A] {n : Usize} (a : Array A n) (i : Usize)
    (bound : i.val<n.val) : Array.index_usize a i=ok (NCV_ArrayFrame.coord a i.val) := by
  obtain ⟨x,call,value⟩:=WP.spec_imp_exists (Array.index_usize_spec a i (by scalar_tac))
  rw [value] at call
  have h : i.val<a.val.length := by rw [a.property];exact bound
  simpa only [NCV_ArrayFrame.coord,List.getElem?_eq_getElem h,Option.getD_some] using call

theorem repeat {A : Type} [Inhabited A] (n : Usize) (x : A) (j : Nat) (bound : j<n.val) :
    NCV_ArrayFrame.coord (Array.repeat n x) j=x := by
  change ((List.replicate n.val x)[j]?).getD default=x
  simp [bound]

#print axioms read
#print axioms repeat
end NCV_ArrayRead
