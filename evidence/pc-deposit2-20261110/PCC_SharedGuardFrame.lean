import PCC_Shared
set_option autoImplicit false
namespace PCC
open PCA
/-- A short-lived child loan does not clear or install parent guard tokens. -/
theorem shared_pure_guards {α : Type} (a : Nat)
    (f : NLF_SdkModel.Payload → α) (s : PCA_State) :
    (withShared a (fun p => Reference.pure (f p)) s).state.liveGuards = s.liveGuards := by
  unfold withShared
  dsimp only
  split
  · rfl
  · split
    · rfl
    · simp only [Reference.pure]
      split <;> rfl
#print axioms shared_pure_guards
end PCC
