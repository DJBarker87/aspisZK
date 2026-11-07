import NMX_DistinctStep
set_option autoImplicit false
noncomputable section
namespace NMX_DistinctPredicate
open Aeneas Aeneas.Std Result AdapterRw NGL_DistinctInduction
/-- Symbolic sparse loop predicate: no concrete descriptor or key comparison is reduced. -/
def before {N : Usize} (a : Array Account N) (index : Usize) : Nat → Usize → Prop
 | 0, _ => True
 | n+1, previous => keyAt a previous ≠ keyAt a index ∧
   before a index n (Usize.wrapping_add previous 1#usize)

def unique {N : Usize} (a : Array Account N) : Nat → Usize → Prop
 | 0, _ => True
 | n+1, index => before a index index.val 0#usize ∧
   unique a n (Usize.wrapping_add index 1#usize)

theorem inner_success {N : Usize} (a : Array Account N) (index : Usize)
 (n : Nat) (previous : Usize) :
 NGL_DistinctInduction.inner a index n previous = ok none ↔ before a index n previous := by
 induction n generalizing previous with
 | zero => simp only [NGL_DistinctInduction.inner,before]
 | succ n ih =>
   rw [NGL_DistinctInduction.inner,before]
   split
   · rename_i h
     constructor
     · intro impossible
       cases impossible
     · intro impossible
       exact False.elim (impossible.1 h)
   · rename_i h
     exact ⟨fun run => ⟨h,(ih _).mp run⟩,fun run => (ih _).mpr run.2⟩

theorem outer_success {N : Usize} (a : Array Account N) (n : Nat) (index : Usize) :
 outer a n index = ok none ↔ unique a n index := by
 induction n generalizing index with
 | zero => simp only [outer,unique]
 | succ n ih =>
   rw [NMX_DistinctStep.success,unique,inner_success,ih]

theorem reference_success {N : Usize} (a : Array Account N) :
 reference a = ok (.Ok ()) ↔ unique a N.val 0#usize := by
 rw [← outer_success]
 rcases NMX_DistinctValues.outer_values a N.val 0#usize with good | bad
 · simp [reference,good]
 · simp [reference,bad]
#print axioms inner_success
#print axioms outer_success
#print axioms reference_success
end NMX_DistinctPredicate
end
