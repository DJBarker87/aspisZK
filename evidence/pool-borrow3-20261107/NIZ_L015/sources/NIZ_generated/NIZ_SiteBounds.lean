import NIZ_LAYOUT
import NIZ_CallbackLayout
set_option autoImplicit false
namespace NIZ_SiteBounds
open NIZ_LAYOUT

def depositCount : DepositMode → Nat
  | .fresh => 10
  | .same => 8
  | .rollover => 11

theorem deposit_guard_bound (mode : DepositMode) (g : Nat)
    (hg : DepositGuard mode g) : g < depositCount mode := by
  cases mode <;> simp only [DepositGuard,depositCount] at * <;>
    rcases hg with hg | ⟨hm,hg⟩ | ⟨hm,hg⟩ <;> simp_all <;> omega
#print axioms deposit_guard_bound

theorem deposit_passed_bound (mode : DepositMode) (o : Nat) (ho : o < 5) :
    depositStart mode + o < depositCount mode := by
  cases mode <;> simp only [depositStart,depositCount] <;> omega
#print axioms deposit_passed_bound

/-- The split-checkpoint account is appended after the complete token suffix. -/
theorem terminal_passed_bound (cursor o checkpoint : Nat) (ho : o < 5) :
    cursor+7+o < cursor+7+5+checkpoint := by omega
#print axioms terminal_passed_bound

theorem pair_passed_bound (marker o checkpoint : Nat) (ho : o < 5) :
    marker+5+o < marker+5+5+checkpoint := by omega
#print axioms pair_passed_bound

theorem callback_passed_bound (marker t checkpoint : Nat)
    (ht : NIZ_CallbackLayout.WithdrawalTouched marker t) :
    t < marker+7+5+checkpoint := by
  rcases ht with ht | ht | ht | ⟨o,ho,ht⟩ <;> omega
#print axioms callback_passed_bound
end NIZ_SiteBounds
