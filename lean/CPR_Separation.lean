import CPR_Persistence
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_Separation
open Aeneas Aeneas.Std Result Hist_Store CPP_BankState CPR_Persistence

def live : Image := ⟨⟨Hist_Nonvacuity.key 0#u8,Hist_Nonvacuity.checkpoint⟩,1⟩
def adjacent (t u : Bool) : Prop := t = false ∧ u = true

def law (loaded : Bool → Unit → Option Image) : Prop :=
  TwoTransactionLaw adjacent (fun _ _ => True) (fun _ _ => live)
    (fun _ _ => live) (fun _ => true) loaded

theorem honest : law (fun _ _ => some live) := by
  intro t u follows key eligible
  rfl

theorem broken : ¬ law (fun _ _ => none) := by
  intro h
  have impossible := h false true ⟨rfl,rfl⟩ () True.intro
  change (none : Option Image) = some live at impossible
  cases impossible

/-- Any inhabited collection of OLD hypotheses is retained unchanged when the
otherwise-unmentioned runtime load is varied. This is a conservative-extension
separation, not a claimed counterexample to the deployed Solana executor. -/
theorem independent (P : Prop) (old : P) :
    ∃ good bad : Bool → Unit → Option Image,
      P ∧ law good ∧ ¬ law bad :=
  ⟨fun _ _ => some live,fun _ _ => none,old,honest,broken⟩

/-- In particular a history instance already supplied for some saved/loaded
bytes constrains THAT pair only, not a new bank loader absent from its type. -/
theorem history_does_not_supply_loader
    (saved loaded : AspisV8R19.DuplexFrames.Bytes)
    (history : S2X.CheckpointVersionBinding saved loaded) :
    Nonempty (S2X.CheckpointVersionBinding saved loaded) ∧
      ¬ law (fun _ _ => none) := ⟨⟨history⟩,broken⟩

#print axioms honest
#print axioms broken
#print axioms independent
#print axioms history_does_not_supply_loader
end AspisR1.CPR_Separation
end
