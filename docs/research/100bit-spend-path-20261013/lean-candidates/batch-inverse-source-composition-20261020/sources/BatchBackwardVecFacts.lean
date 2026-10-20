import BatchBackwardFieldStep
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchBackward.Proof
open R17CurrentM31Semantics alloc.vec

def atM (v : Vec U32) (i : Nat) : ZMod P := decode (v.val.getD i (0#u32))

theorem atM_get (v : Vec U32) (i : Nat) (hi : i < v.val.length) :
    atM v i = decode (v.val[i]'hi) := by
  simp only [atM,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]

theorem atM_set_self (v : Vec U32) (j : Usize) (x : U32) (hj : j.val < v.val.length) :
    atM (v.set j x) j.val = decode x := by
  simp only [atM,Vec.set,List.getD_eq_getElem?_getD,List.getElem?_set_self hj,Option.getD_some]

theorem atM_set_ne (v : Vec U32) (j : Usize) (x : U32) (i : Nat) (hne : j.val ≠ i) :
    atM (v.set j x) i = atM v i := by
  simp only [atM,Vec.set,List.getD_eq_getElem?_getD,List.getElem?_set_ne hne]

theorem set_length (v : Vec U32) (j : Usize) (x : U32) :
    (v.set j x).val.length = v.val.length := by simp only [Vec.set,List.length_set]

#print axioms atM_get
#print axioms atM_set_self
#print axioms atM_set_ne
#print axioms set_length
end AspisR1BatchBackward.Proof
