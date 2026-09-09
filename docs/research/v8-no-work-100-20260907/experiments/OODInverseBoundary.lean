import OODInterpolantRows
import AspisFormal.V5ComponentCQM31TowerExact

/-! Reuse the V7-consumed literal QM31 tower inverse proof, not its q16
sampler or security ledger. This is the exact-field source-form boundary;
the Rust primitive/refinement seam is still separate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 8000
namespace AspisV8.OODInterpolant
noncomputable section
open AspisV5ComponentCQM31TowerExact

theorem exact_inverse_checked (d : Data (K := QM31Exact))
    (success : qm31TryInv (d.h0-d.h1)=some d.inverse) : d.Checked := by
  classical
  have nonzero : d.h0-d.h1 ≠ 0 := by
    intro hz
    rw [hz,qm31TryInv_eq] at success
    simp at success
  have inverse : (d.h0-d.h1)⁻¹=d.inverse := by
    rw [qm31TryInv_eq,if_neg nonzero] at success
    exact Option.some.inj success
  change (d.h0-d.h1)*d.inverse=1
  rw [← inverse]
  exact mul_inv_cancel₀ nonzero

#print axioms exact_inverse_checked
end
end AspisV8.OODInterpolant
