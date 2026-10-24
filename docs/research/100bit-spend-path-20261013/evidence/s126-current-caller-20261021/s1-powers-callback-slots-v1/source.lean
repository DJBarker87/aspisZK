import S1PowersCallbackChainV1
set_option autoImplicit false
namespace AspisS1PowersCallbackChain
open Aeneas Aeneas.Std Result

def slot (N : Usize) (i : Fin N.val) : Usize :=
  UScalar.mk (BitVec.ofNat UScalarTy.Usize.numBits i.val)

theorem slot_val (N : Usize) (i : Fin N.val) : (slot N i).val=i.val := by
  change i.val % 2^UScalarTy.Usize.numBits=i.val
  exact Nat.mod_eq_of_lt (Nat.lt_trans i.isLt N.hBounds)

def slots (N : Usize) : List Usize := List.ofFn (slot N)

theorem slots_length (N : Usize) : (slots N).length=N.val := List.length_ofFn

theorem slots_index (N : Usize) (j : Nat) (hj : j<(slots N).length) :
    ((slots N)[j]'hj).val=j := by
  have bound : j<N.val := by simpa only [slots,List.length_ofFn] using hj
  simpa only [slots,List.getElem_ofFn] using slot_val N ⟨j,bound⟩

#print axioms slot_val
#print axioms slots_length
#print axioms slots_index
end AspisS1PowersCallbackChain
