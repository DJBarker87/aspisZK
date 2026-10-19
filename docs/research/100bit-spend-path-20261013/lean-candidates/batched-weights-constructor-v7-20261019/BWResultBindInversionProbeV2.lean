import AspisR1BatchedWeightsExtraction.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BWResultBindInversionProbeV2
theorem bind_ok_inv {α β : Type} (r : Result α) (f : α → Result β) (y : β)
    (h : (do let x ← r; f x) = .ok y) : ∃ x, r = .ok x ∧ f x = .ok y := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
#print axioms bind_ok_inv
end BWResultBindInversionProbeV2
