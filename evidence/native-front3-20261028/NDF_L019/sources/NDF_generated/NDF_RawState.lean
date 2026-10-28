import Aeneas
set_option autoImplicit false
namespace NDF_RawState
open Aeneas Aeneas.Std Result

def Prefix (bytes : List U8) (at : Nat) (out : List U8) (j : Nat) : Prop :=
  ∀ k, k<j → out[k]?=bytes[at+k]?

theorem initial (bytes out : List U8) (at : Nat) : Prefix bytes at out 0 := by
  intro k h
  omega

theorem extend (bytes out : List U8) (at j : Nat) (value : U8)
    (room : j<out.length) (before : Prefix bytes at out j)
    (read : bytes[at+j]?=some value) :
    Prefix bytes at (out.set j value) (j+1) := by
  intro k bound
  by_cases same : j=k
  · subst k
    simp only [List.getElem?_set_self room]
    exact read.symm
  · rw [List.getElem?_set_ne same]
    exact before k (by omega)

theorem frame (out : List U8) (j k : Nat) (value : U8) (distinct : j≠k) :
    (out.set j value)[k]?=out[k]? := by
  exact List.getElem?_set_ne distinct

theorem complete (bytes out : List U8) (at n : Nat)
    (size : out.length=n) (fit : at+n≤bytes.length) (all : Prefix bytes at out n) :
    out=(bytes.drop at).take n := by
  apply List.ext_getElem?
  intro k
  by_cases active : k<n
  · rw [all k active,List.getElem?_take active,List.getElem?_drop]
  · rw [List.getElem?_eq_none (by omega)]
    symm
    apply List.getElem?_eq_none
    simp only [List.length_take,List.length_drop]
    omega

#print axioms initial
#print axioms extend
#print axioms frame
#print axioms complete
end NDF_RawState
