import R1Z.PV_RDCD4_EncoderLoop
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDCD4_EncoderNext
open PV_RDCD4_EncoderLoop
set_option autoImplicit false

theorem empty {E : Type} (it : PV_RDCD4_ArrayIter194.State E) (i n : Nat) :
    next (⟨⟨[],[]⟩,it,i,n⟩ : Iter E) =
      (none,(⟨⟨[],[]⟩,it,i,n⟩ : Iter E)) := by
  exact PV_RDCD4_Zip194.first_none PV_RDCD4_Chunks194.next
    PV_RDCD4_ArrayIter194.next _ _ (PV_RDCD4_Chunks194.next_empty [])

theorem pair {E : Type} (a b value : E) (tail : List E)
    (it it' : PV_RDCD4_ArrayIter194.State E) (i n : Nat)
    (h : PV_RDCD4_ArrayIter194.next it=(some value,it')) :
    next (⟨⟨a::b::tail,[]⟩,it,i,n⟩ : Iter E) =
      (some ([a,b],value),(⟨⟨tail,[]⟩,it',i,n⟩ : Iter E)) := by
  exact PV_RDCD4_Zip194.both_some PV_RDCD4_Chunks194.next
    PV_RDCD4_ArrayIter194.next _ _ _ _ _
    (PV_RDCD4_Chunks194.next_pair a b tail []) h

#print axioms empty
#print axioms pair
end R1Z.PV_RDCD4_EncoderNext
