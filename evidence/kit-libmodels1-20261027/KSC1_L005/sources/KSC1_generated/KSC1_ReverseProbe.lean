import KSC1_IteratorProbe
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSC1
open KSA_Isolated

def mutDouble : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.IterMut U8) U8 :=
  {iteratorInst := XRn_Join_iterator U8, next_back := XRn_Join_nextBackPair}

theorem reverse_repeats_spent :
    (do let (v,_,_,_) ← XRn_Join_reverseNext mutDouble ⟨spent⟩; ok v) = ok (some 7#u8) := by rfl

theorem reverse_restores_changed_element :
    (do let (_,r,_,back) ← XRn_Join_reverseNext mutDouble ⟨singleton⟩
        ok (back r (some 9#u8)).iter.slice.val) = ok [9#u8] := by rfl

theorem reverse_empty :
    (do let (v,_) ← XRn_Join_nextBackPair {slice := (Array.repeat 0#usize 0#u8).to_slice}
        ok v) = ok none := by rfl

#print axioms reverse_repeats_spent
#print axioms reverse_restores_changed_element
#print axioms reverse_empty
end KSC1
