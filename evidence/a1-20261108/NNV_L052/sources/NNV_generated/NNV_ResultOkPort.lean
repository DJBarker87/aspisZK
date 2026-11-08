import LIB_VResult
set_option autoImplicit false
namespace AspisR1.NNV_ResultOkPort
open Aeneas Result
/-- A successful semantic projection cannot arise from fail, div or Err. -/
theorem value {A E : Type} (r : Result (Except E A)) (fallback : E) (a : A)
 (called : LIB_VResult.value id (.error fallback) r = .ok a) : r = .ok (.ok a) := by
 cases r with
 | fail e => cases called
 | div => cases called
 | ok out => exact congrArg Result.ok called
/-- Recover the raw result at the SAME mapped successful output. -/
theorem mapped {A B : Type} (r : Result A) (f : A → B) (b : B)
 (called : (do let a ← r; Result.ok (f a)) = .ok b) :
 ∃ a, r = .ok a ∧ f a = b := by
 cases r with
 | fail e => cases called
 | div => cases called
 | ok a => exact ⟨a,rfl,Result.ok.inj called⟩
#print axioms value
#print axioms mapped
end AspisR1.NNV_ResultOkPort
