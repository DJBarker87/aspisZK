import Aeneas
set_option autoImplicit false
namespace NHY_ArrayExt
open Aeneas Aeneas.Std Result
def coord {A : Type} [Inhabited A] {n : Usize} (a : Array A n) (j : Nat) : A :=
  a.val[j]?.getD default

def Prefix {A : Type} [Inhabited A] {n : Usize} (a target : Array A n) (k : Nat) : Prop :=
  ∀ j, j<k → j<n.val → coord a j=coord target j

theorem whole {A : Type} [Inhabited A] {n : Usize} (a target : Array A n)
    (pre : Prefix a target n.val) : a=target := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.trans target.property.symm
  · intro j ha ht
    have h : j<n.val := by simpa only [a.property] using ha
    have e:=pre j h h
    simpa only [coord,List.getElem?_eq_getElem ha,List.getElem?_eq_getElem ht,Option.getD_some] using e

#print axioms whole
end NHY_ArrayExt
