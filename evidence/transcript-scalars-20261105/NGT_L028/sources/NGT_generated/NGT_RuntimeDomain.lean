import NGC_DigestBridge
import NFW_ImmutableIO
set_option autoImplicit false
namespace AspisR1.NGT_RuntimeDomain

abbrev View := Nat × Nat

def absorbViews (state tag length payload size : Nat) : List View :=
 [(state,32),(tag,2),(length,4),(payload,size)]
def readViews (state tag : Nat) : List View := [(state,32),(tag,1)]

theorem absorb_domain (state tag length payload size : Nat) (bound : size≤2048) :
 (absorbViews state tag length payload size).length≤9 ∧
 ∀ v∈absorbViews state tag length payload size,v.2≤57607 := by
 constructor
 · decide
 · intro v h
   simp only [absorbViews,List.mem_cons,List.not_mem_nil,or_false] at h
   rcases h with rfl | rfl | rfl | rfl <;> dsimp <;> omega

theorem read_domain (state tag : Nat) :
 (readViews state tag).length≤9 ∧ ∀ v∈readViews state tag,v.2≤57607 := by
 constructor
 · decide
 · intro v h
   simp only [readViews,List.mem_cons,List.not_mem_nil,or_false] at h
   rcases h with rfl | rfl <;> decide

/-- NGC's exact borrowed-descriptor identity and the same admitted memory map
identify every byte, including overlapping and empty views. No hash value or
whole native sampler equality occurs in this statement. -/
theorem same_descriptors {A : Type} (memory : Nat→A) (before after : List View)
 (same : after=before) :
 NFW_ImmutableIO.parts memory after=NFW_ImmutableIO.parts memory before := by
 rw [same]

/-- The physical source maps its mutable LOCAL log/reply allocations outside
all live shared input borrows. This is the retained valid-borrow/ABI domain;
no arbitrary payload byte is fixed to zero. -/
theorem input_frame {A : Type} (memory : Nat→A) (views : List View)
 (writes : List (Nat×A))
 (disjoint : ∀ v∈views,∀ w∈writes,w.1<v.1 ∨ v.1+v.2≤w.1) :
 NFW_ImmutableIO.parts (NFW_ImmutableIO.writes memory writes) views=
 NFW_ImmutableIO.parts memory views :=
 NFW_ImmutableIO.syscall_parts_frame memory views writes disjoint

/-- Full input-byte equality follows from arbitrary fixed-size window facts.
This is induction over memory windows, not repeated calls to the hash oracle. -/
theorem blocks {A : Type} (before after : Nat→A) (base n : Nat)
 (windows : ∀ k<n,∀ i<32,after (base+32*k+i)=before (base+32*k+i)) :
 ∀ i<32*n,after (base+i)=before (base+i) := by
 induction n with
 | zero => intro i hi;omega
 | succ n ih =>
   intro i hi
   by_cases first : i<32*n
   · exact ih (fun k hk j hj => windows k (by omega) j hj) i first
   · have offset : i-32*n<32 := by omega
     have h := windows n (by omega) (i-32*n) offset
     have index : base+32*n+(i-32*n)=base+i := by omega
     simpa only [index] using h

theorem deployed928 {A : Type} (before after : Nat→A) (base : Nat)
 (windows : ∀ k<29,∀ i<32,after (base+32*k+i)=before (base+32*k+i)) :
 ∀ i<928,after (base+i)=before (base+i) := blocks before after base 29 windows

theorem deployed2048 {A : Type} (before after : Nat→A) (base : Nat)
 (windows : ∀ k<64,∀ i<32,after (base+32*k+i)=before (base+32*k+i)) :
 ∀ i<2048,after (base+i)=before (base+i) := blocks before after base 64 windows
#print axioms absorb_domain
#print axioms read_domain
#print axioms same_descriptors
#print axioms input_frame
#print axioms blocks
#print axioms deployed928
#print axioms deployed2048
end AspisR1.NGT_RuntimeDomain
