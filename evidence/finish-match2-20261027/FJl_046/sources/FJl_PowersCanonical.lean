import FJi_SelectedPowers
import Port4C_QueryArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_PowersCanonical
open Aeneas Aeneas.Std Result
/-- Nominal canonicality transport, coordinate by coordinate, into the actual
selected powers constructor. -/
theorem value (x : FIp_DotsAdapter.E) (canonical : Port4C_QueryArithmetic.CanonE x) :
    AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers x) := by
  exact ⟨⟨⟨canonical.1.1,canonical.1.2.1⟩,⟨canonical.1.2.2.1,canonical.1.2.2.2⟩⟩,
    ⟨⟨canonical.2.1,canonical.2.2.1⟩,⟨canonical.2.2.2.1,canonical.2.2.2.2⟩⟩⟩

/-- Imported constructor values, with no re-proof of grouped backend arithmetic. -/
theorem selected (gamma : FIp_DotsAdapter.E) (g : Array FIp_DotsAdapter.E 29#usize)
    (canonical : Port4C_QueryArithmetic.CanonE gamma)
    (run : Tx2N_Powers.powers 29#usize gamma=ok g) :
    FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g) ∧
      ∀ j : Fin 29,FIp_ArrayValue.value (FIp_DotsAdapter.toArray g) j.val=
        CheckpointBytes5Output.ofE gamma^j.val :=
  FJi_SelectedPowers.value gamma g (value gamma canonical) run
#print axioms value
#print axioms selected
end AspisR1.FJl_PowersCanonical
end
