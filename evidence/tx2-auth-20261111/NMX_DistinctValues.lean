import NMX_LeafInstall
set_option autoImplicit false
noncomputable section
namespace NMX_DistinctValues
open Aeneas Aeneas.Std Result AdapterRw
open NGL_DistinctInduction

def Allowed (r : Result Reply) : Prop :=
 r = ok none ∨ r = ok (some (.Err .InvalidArgument))

theorem inner_values {N : Usize} (a : Array Account N) (index : Usize)
 (n : Nat) (previous : Usize) : Allowed (inner a index n previous) := by
 induction n generalizing previous with
 | zero => exact Or.inl rfl
 | succ n ih =>
   rw [NGL_DistinctInduction.inner]
   split
   · exact Or.inr rfl
   · exact ih _

theorem outer_values {N : Usize} (a : Array Account N) (n : Nat) (index : Usize) :
 Allowed (outer a n index) := by
 induction n generalizing index with
 | zero => exact Or.inl rfl
 | succ n ih =>
   rcases inner_values a index index.val 0#usize with normal | rejected
   · simp only [outer,normal,bind_tc_ok]
     exact ih _
   · simp only [outer,rejected,bind_tc_ok]
     exact Or.inr rfl

theorem reference_values {N : Usize} (a : Array Account N) :
 reference a = ok (.Ok ()) ∨ reference a = ok (.Err .InvalidArgument) := by
 rcases outer_values a N.val 0#usize with normal | rejected
 · simp [reference,normal]
 · simp [reference,rejected]
#print axioms inner_values
#print axioms outer_values
#print axioms reference_values
end NMX_DistinctValues
end
