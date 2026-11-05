import NHB_Observation
set_option autoImplicit false
namespace AspisR1.NHB_DomainSplit

def Stopped (n d : Nat) : Prop := n=22 ∨ d=64
def Low (n d : Nat) : Prop := d<64 ∧ n≤10
def Middle (n d : Nat) : Prop := d<64 ∧ 11≤n ∧ n≤15
def High (n d : Nat) : Prop := d<64 ∧ 16≤n ∧ n<22

theorem complete (n d : Nat) (length : n≤22) (draws : d≤64) :
    Stopped n d ∨ Low n d ∨ Middle n d ∨ High n d := by
  unfold Stopped Low Middle High
  omega

/-- Bounds alone cannot license the smaller checked word domain. -/
theorem bounds_do_not_imply_low_or_stop :
    ¬(∀ n d : Nat, n≤22 → d≤64 → Stopped n d ∨ Low n d) := by
  intro claim
  have bad := claim 11 11 (by omega) (by omega)
  unfold Stopped Low at bad
  omega

theorem middle_is_missing_from_other_cases :
    Middle 11 11 ∧ ¬Stopped 11 11 ∧ ¬Low 11 11 ∧ ¬High 11 11 := by
  unfold Stopped Low Middle High
  omega

#print axioms complete
#print axioms bounds_do_not_imply_low_or_stop
#print axioms middle_is_missing_from_other_cases
end AspisR1.NHB_DomainSplit
