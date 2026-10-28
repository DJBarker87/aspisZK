import NCV_ByteStep
set_option autoImplicit false
namespace NCV_ArrayFrame
open Aeneas Aeneas.Std Result

def coord {A : Type} [Inhabited A] {n : Usize} (a : Array A n) (j : Nat) : A :=
  a.val[j]?.getD default

theorem set_at {A : Type} [Inhabited A] {n : Usize} (a : Array A n)
    (i : Usize) (x : A) (j : Nat) (hi : i.val<n.val) (hj : j<n.val) :
    coord (a.set i x) j = if i.val=j then x else coord a j := by
  have len : a.val.length=n.val := a.property
  change ((a.val.set i.val x)[j]?).getD default =
    if i.val=j then x else a.val[j]?.getD default
  simp only [List.getElem?_eq_getElem (show j < (a.val.set i.val x).length by simpa using hj),
    List.getElem_set,List.getElem?_eq_getElem (show j<a.val.length by omega),Option.getD_some]

/-- Initial segment already written by earlier iterations. -/
def Prefix {A : Type} [Inhabited A] {n : Usize} (a target : Array A n) (k : Nat) : Prop :=
  ∀ j, j<k → j<n.val → coord a j=coord target j

theorem extend {A : Type} [Inhabited A] {n : Usize} (a target : Array A n)
    (i : Usize) (hi : i.val<n.val) (pre : Prefix a target i.val) :
    Prefix (a.set i (coord target i.val)) target (i.val+1) := by
  intro j hj hn
  rw [set_at a i _ j hi hn]
  by_cases same : i.val=j
  · simp only [same,ite_true]
  · rw [if_neg same]
    exact pre j (by omega) hn

theorem whole {A : Type} [Inhabited A] {n : Usize} (a target : Array A n)
    (pre : Prefix a target n.val) : a=target := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.trans target.property.symm
  · intro j ha ht
    have h : j<n.val := by simpa only [a.property] using ha
    have e:=pre j h h
    simpa only [coord,List.getElem?_eq_getElem ha,List.getElem?_eq_getElem ht,Option.getD_some] using e

#print axioms set_at
#print axioms extend
#print axioms whole
end NCV_ArrayFrame
