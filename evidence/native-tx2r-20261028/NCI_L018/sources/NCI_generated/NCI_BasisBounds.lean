import Init
set_option autoImplicit false
namespace AspisR1.NCI_BasisBounds

theorem stage_half (stage : Nat) (hs : stage < 6) : 2^stage ≤ 32 := by
  have cases : stage=0 ∨ stage=1 ∨ stage=2 ∨ stage=3 ∨ stage=4 ∨ stage=5 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem write_domain (stage j : Nat) (hs : stage<6) (hj : j<2^stage) :
    2^stage+j<64 ∧ j<64 ∧ 2^stage+j<256 := by
  have half := stage_half stage hs
  omega

theorem doubled (stage : Nat) (hs : stage<6) : 2^stage*2=2^(stage+1) ∧ 2^(stage+1)≤64 := by
  constructor
  · exact (Nat.pow_succ 2 stage).symm
  · have h := stage_half stage hs
    rw [Nat.pow_succ]; omega

theorem active_stage (stage : Nat) (hs : stage≤6) (active : 2^stage<64) : stage<6 := by
  by_cases h : stage<6
  · exact h
  · have eq : stage=6 := by omega
    subst stage
    contradiction

theorem terms_advance (next terms : Nat) (hn : 10≤next ∧ next<22) (ht : terms=next-10) :
    terms<12 ∧ terms+1=(next+1)-10 ∧ terms+1≤12 := by omega

theorem flushes (terms : Nat) (ht : terms<12) (hf : terms%4=3) :
    terms=3 ∨ terms=7 ∨ terms=11 := by omega
#print axioms stage_half
#print axioms write_domain
#print axioms doubled
#print axioms active_stage
#print axioms terms_advance
#print axioms flushes
end AspisR1.NCI_BasisBounds
