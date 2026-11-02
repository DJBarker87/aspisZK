import PV_EVH_StackAdmission
set_option autoImplicit false
namespace PV_EVH_StackRegions
open PV_EVH_StackZero (Slot State Cleared drop)

/-- Numeric separation is a consequence required of the actual source-frame
interpretation; fresh ghost lifetime identities alone cannot establish it. -/
def Separate (a b : Slot) : Prop :=
  a.address+a.initialized ≤ b.address ∨ b.address+b.initialized ≤ a.address

theorem symmetric (a b : Slot) (h : Separate a b) : Separate b a := h.symm

theorem outside (a b : Slot) (h : Separate a b) (i : Nat)
    (hi : i < b.initialized) : PV_EVH_StackAdmission.Outside a (b.address+i) := by
  unfold Separate at h
  unfold PV_EVH_StackAdmission.Outside
  omega

theorem drop_keeps_clear (a b : Slot) (w : State)
    (h : Separate a b) (hc : Cleared b w) : Cleared b (drop a w) := by
  intro i hi
  exact (PV_EVH_StackZero.outside_preserved a w (b.address+i)
    (outside a b h i hi)).trans (hc i hi)

theorem write_keeps_clear (a b : Slot) (bytes : PV_RJ4IDB.Bytes) (w : State)
    (h : Separate a b) (hc : Cleared b w) :
    Cleared b (PV_EVH_StackAdmission.write a bytes w) := by
  intro i hi
  exact (PV_EVH_StackAdmission.write_outside a bytes w (b.address+i)
    (outside a b h i hi)).trans (hc i hi)

#print axioms symmetric
#print axioms outside
#print axioms drop_keeps_clear
#print axioms write_keeps_clear
end PV_EVH_StackRegions
