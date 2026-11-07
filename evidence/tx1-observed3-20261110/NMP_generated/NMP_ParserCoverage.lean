import NLZ_Resources
set_option autoImplicit false
namespace AspisR1.NMP_ParserCoverage
open Aeneas Aeneas.Std
open NLZ_Resources
/-- Counterexample to constructor coverage, NOT to the frozen parser. Both
objects are valid and initialized; the free Prefix reply's root may refer to a
second live allocation, while the current Rust constructor selects only input
views. This is stronger than the predecessor's empty-heap observation. -/
def object (n owner : Nat) : Object :=
 ⟨List.replicate n 0#u8,1,owner,List.replicate n true⟩
def heap : Heap where
 objects := fun i => if i=0 then some (object 14759 0) else if i=1 then some (object 32 1) else none
 external := fun _ => []
 metadata := fun _ => []
 borrowCount := fun _ => 0
def input : Window := ⟨0,0,13831⟩
def root : Window := ⟨1,0,32⟩
theorem valid : View heap input (List.replicate 13831 0#u8) ∧
 View heap root (List.replicate 32 0#u8) := by
 constructor
 · refine ⟨object 14759 0,?_,?_,?_,?_,?_⟩
   · rfl
   · simp only [input,object,List.length_replicate,Nat.zero_add]
     omega
   · simp only [input,List.length_replicate]
   · simp only [input,object,List.drop_zero,List.take_replicate]
     rw [Nat.min_eq_left (by omega)]
   · simp only [input,object,List.drop_zero,List.take_replicate]
     rw [Nat.min_eq_left (by omega)]
 · refine ⟨object 32 1,?_,?_,?_,?_,?_⟩
   · rfl
   · simp only [root,object,List.length_replicate,Nat.zero_add,Nat.le_refl]
   · simp only [root,List.length_replicate]
   · simp only [root,object,List.drop_zero,List.take_replicate,Nat.min_self]
   · simp only [root,object,List.drop_zero,List.take_replicate,Nat.min_self]
theorem not_input_backed : root.allocation ≠ input.allocation := by
 decide
#print axioms valid
#print axioms not_input_backed
end AspisR1.NMP_ParserCoverage
