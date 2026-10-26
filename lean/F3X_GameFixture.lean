import CPR_DataPersistence
import CPP_BankHistory
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_GameFixture
open AspisV8R19.DuplexFrames

def next (t u : Bool) : Prop := t=false ∧ u=true
def ordinary (_ : Bool) (_ : Nat) : Prop := True
def before (initial : CPP_BankState.Bank) (_ : Bool) (key : Nat) :=
  CPR_DataPersistence.snapshot initial key
def tentative (final : CPP_BankState.Bank) (_ : Bool) (key : Nat) :=
  CPR_DataPersistence.snapshot final key
def success (_ : Bool) : Bool := true
def loaded (final : CPP_BankState.Bank) (_ : Bool) (key : Nat) :=
  CPR_DataPersistence.visible (CPR_DataPersistence.snapshot final key)

/-- A symbolic two-entry model inhabits all RuntimePersistence equations.
This is consistency of the named trust item, not an Agave implementation
proof. The final bank may contain a nonempty protected action history. -/
theorem RuntimePersistence (initial final : CPP_BankState.Bank) :
    CPR_DataPersistence.TwoTransactionLaw next ordinary (before initial) (tentative final)
      success (loaded final) := by
  intro t u adjacent key eligible
  rfl

theorem game (initial final : CPP_BankState.Bank) (key : Nat) :
    next false true ∧ ordinary false key ∧ success false=true ∧
    tentative final false key=CPR_DataPersistence.snapshot final key ∧
    before initial false key=CPR_DataPersistence.snapshot initial key := by
  exact ⟨⟨rfl,rfl⟩,trivial,rfl,rfl,rfl⟩

#print axioms RuntimePersistence
#print axioms game
end AspisR1.F3X_GameFixture
end
