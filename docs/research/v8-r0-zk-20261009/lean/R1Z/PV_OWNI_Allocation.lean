import R1Z.PV_OWNI_EmptyVec
set_option autoImplicit false
namespace R1Z.PV_OWNI_Allocation
open PV_OWN_Heap PV_OWN_Operations PV_W_Threading

theorem success {S X E : Type}
 (primitive : Request → S → Outcome E (Option Nat) × S)
 (w : State S X) (p owner capacity : Nat) (s : S)
 (h:primitive ⟨capacity*24,8⟩ w.allocator=(.ok (some p),s)) :
 allocate primitive ⟨capacity*24,8⟩ owner w=
 ⟨.ok (some (PV_OWNI_EmptyVec.token w.memory p)),
  {w with allocator:=s,memory:=PV_OWNI_EmptyVec.initialized w.memory p owner capacity},
  [(w,.allocate (capacity*24) 8)]⟩ := by
 simp only [allocate,emit,h,PV_OWNI_EmptyVec.token,PV_OWNI_EmptyVec.initialized]

theorem null {S X E : Type}
 (primitive : Request → S → Outcome E (Option Nat) × S)
 (w : State S X) (owner capacity : Nat) (s : S)
 (h:primitive ⟨capacity*24,8⟩ w.allocator=(.ok none,s)) :
 allocate primitive ⟨capacity*24,8⟩ owner w=
 ⟨.ok none,{w with allocator:=s},[(w,.allocate (capacity*24) 8)]⟩ := by
 simp only [allocate,emit,h]

theorem no_stale_loan (m : Memory) (p : Nat)
 (loans:∀ l ∈ m.loans,l.token.generation≤m.generations l.token.address) :
 NoLoans m (PV_OWNI_EmptyVec.token m p) := by
 intro l hl eq
 have bound:=loans l hl
 rw [eq] at bound
 change m.generations p+1≤m.generations p at bound
 omega
#print axioms success
#print axioms null
#print axioms no_stale_loan
end R1Z.PV_OWNI_Allocation
