import NJA_ParentCut

set_option autoImplicit false
namespace NJA_RejectCut
open Aeneas Aeneas.Std
abbrev Digests := Array NJA_ParentCut.Digest 16#usize
abbrev Indices := Array U32 16#usize

def cell {α : Type} {n : Usize} (a : Array α n) (i : Fin n.val) : α :=
 a.val[i.val]'(by rw [a.property];exact i.isLt)

theorem array_ext {α : Type} {n : Usize} (a b : Array α n)
 (h : ∀ i : Fin n.val, cell a i = cell b i) : a=b := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact a.property.trans b.property.symm
 · intro i hi _
   exact h ⟨i,by rwa [a.property] at hi⟩

-- Coordinate assertions certified separately for constant n=0 and n=17.
-- No whole-buffer/model endpoint equality is assumed.
structure Cut (before after : Indices) (values post : Digests) (answer : Bool) where
 rejected : answer=false
 indices : ∀ i : Fin (16#usize).val, cell after i = cell before i
 bytes : ∀ (i : Fin (16#usize).val) (k : Fin 32),
   NJA_ParentCut.byte (cell post i) k = NJA_ParentCut.byte (cell values i) k

theorem full_frame (before after : Indices) (values post : Digests) (answer : Bool)
 (cut : Cut before after values post answer) :
 answer=false ∧ after=before ∧ post=values := by
 refine ⟨cut.rejected,array_ext _ _ cut.indices,?_⟩
 apply array_ext
 intro i
 exact NJA_ParentCut.ext _ _ (cut.bytes i)

theorem short_circuit (n : Nat) (invalid : n=0 ∨ 16<n) (later : Bool) :
 (if n=0 ∨ n>16 then false else later) = false := by simp [invalid]

#print axioms array_ext
#print axioms full_frame
#print axioms short_circuit
end NJA_RejectCut
