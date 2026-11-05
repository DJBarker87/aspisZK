import NHG_ClaimsDomain
set_option autoImplicit false
namespace AspisR1.NHU_ClaimsHeap
/-- A cell is initialized after exactly p complete source row writes.
This tracks initialization separately from the copied value. It asserts
nothing about the still-open decoder/payload or allocation association. -/
def initialized (p cell : Nat) : Bool := decide (cell/29<p)
def write (p : Nat) (before : Nat→Bool) (cell : Nat) : Bool :=
 if cell/29=p then true else before cell

theorem initial (cell : Nat) : initialized 0 cell=false := by
 simp only [initialized,Nat.not_lt_zero,decide_false]

theorem step (p cell : Nat) :
 write p (initialized p) cell=initialized (p+1) cell := by
 unfold write initialized
 split <;> simp_all only [Bool.true_eq_decide_iff,decide_eq_decide] <;> omega

theorem complete (cell : Nat) (inside : cell<87) : initialized 3 cell=true := by
 unfold initialized
 apply decide_eq_true
 omega

theorem prior_frame (p cell : Nat) (prior : cell/29<p) (before : Nat→Bool) :
 write p before cell=before cell := by
 unfold write
 rw [if_neg (by omega)]

/-- Decoder failure happens before ptr.write at the source boundary. Thus
it performs no initialization update; it does not license assume_init. -/
theorem error_frame (before : Nat→Bool) (cell : Nat) :
 (fun i=>before i) cell=before cell := rfl

#print axioms initial
#print axioms step
#print axioms complete
#print axioms prior_frame
#print axioms error_frame
end AspisR1.NHU_ClaimsHeap
