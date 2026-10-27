import FJl_PowersCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_PowersLiteral
open Aeneas Aeneas.Std Result
/-- Each of the SAME 29 selected coefficients is the power of the literal
gamma, preserving the native array and every coordinate. -/
theorem value (gamma : FIp_DotsAdapter.E) (g : Array FIp_DotsAdapter.E 29#usize)
    (literal : AspisWideTower.WideExact)
    (canonical : Port4C_QueryArithmetic.CanonE gamma)
    (run : Tx2N_Powers.powers 29#usize gamma=ok g)
    (same : CheckpointBytes5Output.ofE gamma=literal) :
    FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g) ∧
      ∀ j : Fin 29,FIp_ArrayValue.value (FIp_DotsAdapter.toArray g) j.val=literal^j.val := by
  obtain ⟨hc,hv⟩ := FJl_PowersCanonical.selected gamma g canonical run
  exact ⟨hc,fun j=>by rw [hv j,same]⟩
#print axioms value
end AspisR1.FJl_PowersLiteral
end
