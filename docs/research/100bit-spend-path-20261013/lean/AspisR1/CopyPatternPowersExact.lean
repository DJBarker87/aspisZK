import AspisR1.CopyPatternPowerLoop
import AspisR1.ArrayZeroExact

/-! Actual initialized source power loop equals the retained Copy powers. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternPowersExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CopyPatternPowerLoop AspisR1.CopyPatternPowerModel
open AspisR1.ArrayZeroExact AspisR1.ArrayUpdateCanonicalExact
open AspisR1.CopyEndpointExact

theorem initialized_powers_exact (lambda : field.QM31)
    (hlambda : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM lambda) :
    ∃ out, Loop lambda (Array.repeat 16#usize field.QM31.ZERO) lambda 0#usize =
        .ok (out,16#usize) ∧
      CanonicalArray out ∧ decodedCells out = R0P.copyPowers (AspisR1.CopyPatternPowerLoop.decode lambda) := by
  obtain ⟨out,hrun,hcanonical,hvalues⟩ := powers_loop_success_fuel
    lambda (Array.repeat 16#usize field.QM31.ZERO) lambda 0#usize 16
    (by scalar_tac) hlambda repeat_zero_canonical hlambda
    (by simpa only [UScalar.ofNatCore_val_eq, powerAt_zero])
    (by intro j hj; simp only [UScalar.ofNatCore_val_eq] at hj; omega)
  refine ⟨out,hrun,hcanonical,?_⟩
  funext j
  change AspisR1.CopyPatternPowerLoop.decode (cells out j) =
    R0P.copyPowers (AspisR1.CopyPatternPowerLoop.decode lambda) j
  rw [retained_copyPowers]
  exact hvalues j

#print axioms initialized_powers_exact
end
end AspisR1.CopyPatternPowersExact
