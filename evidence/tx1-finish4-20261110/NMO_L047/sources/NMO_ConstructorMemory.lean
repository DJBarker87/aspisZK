import NLU_State
set_option autoImplicit false
namespace AspisR1.NMO_ConstructorMemory
open Aeneas Aeneas.Std
abbrev Memory := Nat→Option U32
def write (m : Memory) (index : Nat) (value : U32) : Memory :=
 fun address=>if address=index then some value else m address
/-- Symbolic model of the generated in-place writes, not aggregate reduction. -/
def populate : Nat→(Nat→U32)→Memory→Memory
 | 0,_,m=>m
 | n+1,values,m=>write (populate n values m) n (values n)
theorem read_populated (n : Nat) (values : Nat→U32) (before : Memory)
 (index : Nat) (inside : index<n) : populate n values before index=some (values index) := by
 induction n with
 | zero=>omega
 | succ n ih=>
  by_cases last : index=n
  · subst index;simp only [populate,write,ite_true]
  · have earlier : index<n:=by omega
    simp only [populate,write,if_neg last]
    exact ih earlier
theorem frame (n : Nat) (values : Nat→U32) (before : Memory)
 (address : Nat) (outside : n≤address) : populate n values before address=before address := by
 induction n with
 | zero=>rfl
 | succ n ih=>
  have different : address≠n:=by omega
  simp only [populate,write,if_neg different]
  exact ih (by omega)
/-- All 348 scalar words of the fresh 1392-byte Claims block are populated.
The arbitrary word values stay independent; no canonicality is assumed. -/
theorem claims_block (values : Nat→U32) (before : Memory) :
 (∀ index,index<348→populate 348 values before index=some (values index)) ∧
 (∀ address,348≤address→populate 348 values before address=before address) :=
 ⟨fun index inside=>read_populated 348 values before index inside,
  fun address outside=>frame 348 values before address outside⟩
#print axioms read_populated
#print axioms frame
#print axioms claims_block
end AspisR1.NMO_ConstructorMemory
