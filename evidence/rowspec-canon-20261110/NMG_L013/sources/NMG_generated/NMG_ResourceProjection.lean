import NMG_Resource
set_option autoImplicit false
namespace NMG_ResourceProjection
open NMG_Resource
/-- Value-only forgetful map; no frozen interpreter is asserted. -/
structure Enriched (Value : Type) where
 value : Value
 heap : Heap
 actions : List Action
def erase {Value : Type} (x : Enriched Value) : Value := x.value
def emptyHeap : Heap := ⟨fun _=>none,0⟩
def ownedHeap : Heap := ⟨fun id=>if id=0 then some ⟨[],0,0⟩ else none,1⟩
/-- Countermodel to reconstruction from a value-only carrier. It does NOT
assert either enriched observation is the frozen implementation's trace. -/
theorem not_injective {Value : Type} (value : Value) :
 ∃ a b : Enriched Value, erase a=erase b ∧ a.heap.cells 0≠b.heap.cells 0 := by
 refine ⟨⟨value,emptyHeap,[]⟩,⟨value,ownedHeap,[]⟩,rfl,?_⟩
 change (none : Option Allocation)≠some ⟨[],0,0⟩
 exact Option.noConfusion
#print axioms not_injective
end NMG_ResourceProjection
