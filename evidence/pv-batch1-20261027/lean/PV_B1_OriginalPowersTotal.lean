import PV_B1_PowersTotal
set_option autoImplicit false
noncomputable section
namespace PV_B1_OriginalPowersTotal
open Aeneas Aeneas.Std Result
open PV_B1_254 PV_B1_PowersControl
theorem total (N : Usize) (x : W) :
    ∃ y, PV_B1_PowersOriginal.weights.powers N x=ok y := by
  rw [←PV_B1_PowersBridge.op254_copy_equal_original]
  exact PV_B1_PowersTotal.total N x
-- Both variants preserve every raw limb and report no modeled failure.
theorem no_error (N : Usize) (x : W) (e : Error) :
    PV_B1_PowersOriginal.weights.powers N x≠fail e := by
  obtain ⟨y,hy⟩ := total N x
  rw [hy]; intro h; cases h
#print axioms total
#print axioms no_error
end PV_B1_OriginalPowersTotal
