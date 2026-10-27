import LPl_ExpandResult
set_option autoImplicit false
namespace LPl.Expand
/-- Exhaustive constant-offset classes. The last class has four alternatives;
    no symbolic destination-offset SAT shape is repeated. -/
theorem covered (row : Nat) (bound : row<116) :
    ∃ c k : Nat, c<15 ∧ k<8 ∧ row=8*c+k ∧ (c=14 → k<4) := by
  refine ⟨row/8,row%8,?_,?_,?_,?_⟩ <;> omega

/-- All actual expanded semantic/y1 caller counts fall within the certified
    class table; no restriction on any field byte or initial output byte. -/
theorem caller_rows (n row : Nat) (bound : n≤1856) (live : row<n/16) : row<116 := by omega

#print axioms covered
#print axioms caller_rows
end LPl.Expand
