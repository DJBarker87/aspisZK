import NNH_Run5bHost
set_option autoImplicit false
namespace AspisR1.NNV_WeakErrRestatement
open Aeneas Aeneas.Std Result
/-- The approved weak clause follows from exact Rust Err, but does not select
an error payload or assert termination. Quantifiers and Ok carrier stay fixed. -/
theorem exact_implies_weak {A E : Type} (model : Result (core.result.Result A E))
 (exact_ : ∃ e, model = .ok (.Err e)) :
 ¬ ∃ saved, model = .ok (.Ok saved) := by
 obtain ⟨e,h⟩ := exact_
 rw [h]
 rintro ⟨saved,impossible⟩
 cases impossible
#print axioms exact_implies_weak
end AspisR1.NNV_WeakErrRestatement
