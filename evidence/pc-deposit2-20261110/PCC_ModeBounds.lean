import PCC_CountClauses
set_option autoImplicit false
namespace PCC
open PCA

def modeCount : Mode → Nat
  | .fresh .. => 10 | .same .. => 8 | .rollover .. => 11
def modeStart : Mode → Nat
  | .fresh .. => 3 | .same .. => 3 | .rollover .. => 4

/-- The complete count split of (c-c) is independent of AccountInfo Arbitrary.
A future harness must use each admitted count, not choose a bound. -/
theorem reached_mode_count (mode : Mode) (s : PCA_State)
    (h : (countReference (modeCount mode) s).reply = .ok ()) :
    s.accountCount = modeCount mode := count_success _ _ h

theorem token_window_bound (mode : Mode) (offset : Nat) (h : offset < 5) :
    modeStart mode + offset < modeCount mode := by
  cases mode <;> simp only [modeStart,modeCount] <;> omega

theorem mode_count_values (mode : Mode) :
    modeCount mode = 8 ∨ modeCount mode = 10 ∨ modeCount mode = 11 := by
  cases mode <;> simp [modeCount]
#print axioms reached_mode_count
#print axioms token_window_bound
#print axioms mode_count_values
end PCC
