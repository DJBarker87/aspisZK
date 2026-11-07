import NMW_RowSpecs
set_option autoImplicit false
noncomputable section
namespace NMW_Carrier
open Aeneas Aeneas.Std AspisR1 NMW_Outcome NMW_FullDispatch
/-- A carrier adapter is bijective: it cannot erase Box owners, guards,
account metadata, error payloads, effects or stopped-prefix information. -/
def outcome {W E V F : Type} (world : W ≃ V) (event : E ≃ F) :
 Outcome W E → Outcome V F
 | .returned reply post history => .returned reply (world post) (history.map event)
 | .stopped why history => .stopped why (history.map event)

def args {A B : Type} (accounts : Slice A ≃ Slice B) (input : Args A) : Args B :=
 ⟨input.program,accounts input.accounts,input.data⟩

theorem outcome_inverse {W E V F : Type} (world : W ≃ V) (event : E ≃ F)
 (value : Outcome W E) : outcome world.symm event.symm (outcome world event value) = value := by
 cases value <;> simp [outcome,List.map_map]

theorem outcome_injective {W E V F : Type} (world : W ≃ V) (event : E ≃ F) :
 Function.Injective (outcome world event) := by
 intro left right same
 have mapped := congrArg (outcome world.symm event.symm) same
 simpa only [outcome_inverse] using mapped

theorem args_data {A B : Type} (accounts : Slice A ≃ Slice B) (input : Args A) :
 (args accounts input).data = input.data := rfl

theorem args_inverse {A B : Type} (accounts : Slice A ≃ Slice B) (input : Args A) :
 args accounts.symm (args accounts input) = input := by
 cases input
 simp [args]
#print axioms outcome_inverse
#print axioms outcome_injective
#print axioms args_data
#print axioms args_inverse
end NMW_Carrier
end
