import Aeneas
set_option autoImplicit false
namespace NJC_ScanPartition

/-- The source's26 scalar reads followed by one K cover the same30 words. -/
theorem thirty (p : Nat → Prop) :
 ((∀ j,j<26→p j) ∧ (∀ j,j<4→p (26+j))) ↔ ∀ j,j<30→p j := by
 constructor
 · rintro ⟨a,b⟩ j bound
   by_cases low:j<26
   · exact a j low
   · have h:=b (j-26) (by omega);simpa only [Nat.add_sub_of_le (by omega : 26≤j)] using h
 · intro all
   exact ⟨fun j h=>all j (by omega),fun j h=>all (26+j) (by omega)⟩

/-- Symbolic block decomposition; used at4 limbs per K and8 per E. No
concrete Finset enumeration or full buffer normalization occurs. -/
theorem blocks (width n : Nat) (positive : 0<width) (p : Nat → Prop) :
 (∀ i,i<n→∀ j,j<width→p (width*i+j)) ↔ ∀ k,k<width*n→p k := by
 constructor
 · intro all k bound
   have quotient : k/width<n := (Nat.div_lt_iff_lt_mul positive).mpr (by simpa [Nat.mul_comm] using bound)
   have h:=all (k/width) quotient (k%width) (Nat.mod_lt _ positive)
   have eq:width*(k/width)+k%width=k := by have h:=Nat.mod_add_div k width;omega
   simpa only [eq] using h
 · intro all i hi j hj
   apply all (width*i+j)
   have mul:=Nat.mul_le_mul_left width (Nat.succ_le_of_lt hi)
   simp only [Nat.mul_succ] at mul
   omega

/-- Frozen scan order interleaves each120-byte lane with its32-byte K suffix.
The adopted parser scans all608 bytes contiguously. Both visit exactly the
same152 words. Reordering is permitted here only with the separately proved
pure frame/no-oracle-event law, never on an oracle-bearing child. -/
theorem opening (p : Nat → Prop) :
 (∀ s,s<4→(∀ j,j<30→p (30*s+j)) ∧ (∀ j,j<8→p (120+8*s+j))) ↔
 ∀ k,k<152→p k := by
 constructor
 · intro all k bound
   by_cases low:k<120
   · have h:=(all (k/30) (by omega)).1 (k%30) (by omega)
     have eq:30*(k/30)+k%30=k := by omega
     simpa only [eq] using h
   · have h:=(all ((k-120)/8) (by omega)).2 ((k-120)%8) (by omega)
     have eq:120+8*((k-120)/8)+(k-120)%8=k := by omega
     simpa only [eq] using h
 · intro all s hs
   exact ⟨fun j hj=>all (30*s+j) (by omega),fun j hj=>all (120+8*s+j) (by omega)⟩

#print axioms thirty
#print axioms blocks
#print axioms opening
end NJC_ScanPartition
