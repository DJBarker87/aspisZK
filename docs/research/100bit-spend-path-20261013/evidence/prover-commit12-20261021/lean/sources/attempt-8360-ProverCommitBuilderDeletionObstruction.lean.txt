import R1Z.PrivacyR1HeadlineOwnedClosed

/-! A concrete counterexample to removing the arbitrary-input builder premise.
The input's build function is not constrained by a scalar/callback theorem.
This does not refute the intended concrete Rust builder. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitBuilderDeletionObstruction
open R0P R0Z.JointView
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis

theorem i_not_base : PrivacyR1AcctBasis.i ∉ F := by
  intro hi
  obtain ⟨a, ha⟩ := RingHom.mem_fieldRange.mp hi
  have heq := congrArg (fun z : K => z.re.re.im) ha
  rw [PrivacyR1AcctBasis.base_coordinates] at heq
  change (0 : ZMod AspisCircleGroupOrder.P) = 1 at heq
  exact zero_ne_one heq

def badInput (pub : Public K) : HonestProver K where
  Instance := Unit
  transport := AspisR1.rowEquiv
  «public» := fun _ => pub
  build := fun _ _ _ => PrivacyR1AcctBasis.i

theorem builder_premise_false {CommitHandle : Type}
    (pub : Public K) (handle : CommitHandle) :
    ¬ PrivacyR1Headline.BuilderPremises
      (PhaseWireLog2Bin.honest (badInput pub)) B (pub, handle) := by
  intro premises
  have sound := (premises () rfl).2 () rfl
  have typed := sound.baseTyped (0 : Fin 29) (by decide) (0 : Fin 1024)
  exact i_not_base typed

theorem no_universal_builder_discharge {CommitHandle : Type}
    (pub : Public K) (handle : CommitHandle) :
    ¬ (∀ input : HonestProver K,
      PrivacyR1Headline.BuilderPremises
        (PhaseWireLog2Bin.honest input) B (pub, handle)) := by
  intro all
  exact builder_premise_false pub handle (all (badInput pub))

#print axioms i_not_base
#print axioms builder_premise_false
#print axioms no_universal_builder_discharge
end R1Z.ProverCommitBuilderDeletionObstruction
