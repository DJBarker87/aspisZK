import NJS_RuntimeDigest
set_option autoImplicit false
namespace NJS_DigestDomains
open Aeneas Aeneas.Std AspisR1

def leafParts (tag : U8) (value : Slice U8) (salt : Array U8 32#usize) :=
 Port4B_LeafCode.parts tag value salt.to_slice

theorem leaf (tag : U8) (value : Slice U8) (salt : Array U8 32#usize)
 (width : value.val.length≤480) :
 (leafParts tag value salt).val.length≤9 ∧
 ∀ part∈(leafParts tag value salt).val,part.val.length≤57607 := by
 have saltLength : salt.val.length=32 := salt.property
 constructor
 · change 3≤9;decide
 · intro part member
   simp only [leafParts,Port4B_LeafCode.parts,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl
   · change 2≤57607;decide
   · omega
   · change salt.val.length≤57607;omega

/-- Universal closure of the native parent's nine descriptor-length assertions.
No data equality follows from a numerical address assumption. -/
theorem parent (lengths : List Nat) (count : lengths.length=9)
 (tag : lengths[0]?=some 1)
 (children : ∀ i,i<8 → lengths[i+1]?=some 32) :
 lengths.length≤9 ∧ ∀ n∈lengths,n≤57607 := by
 refine ⟨by omega,?_⟩
 intro n member
 obtain ⟨i,hi,entry⟩ := List.mem_iff_getElem.mp member
 have cell : lengths[i]?=some n := by simpa only [List.getElem?_eq_getElem hi,entry]
 by_cases zero : i=0
 · subst i;rw [tag] at cell;cases cell;decide
 · have prior : i-1<8 := by omega
   have point := children (i-1) prior
   have shift : i-1+1=i := by omega
   rw [shift,cell] at point;cases point;decide
#print axioms leaf
#print axioms parent
end NJS_DigestDomains
