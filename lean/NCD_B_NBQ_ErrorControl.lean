-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_NBG_Error
set_option autoImplicit false
noncomputable section
namespace NBQ_ErrorControl
open Aeneas Aeneas.Std Result
/-- The soundness observation discards formatting and log contents. Runtime
logging preserves account data, while its own private state may change. -/
theorem frame {State Accounts : Type} (accounts : State → Accounts)
    (log : String → State → Result State) (error : NBG_Error.E)
    (before after : State)
    (returned : log (NBG_Error.message error) before = ok after)
    (logFrame : ∀ message s t, log message s = ok t → accounts t = accounts s) :
    NBG_Error.run log error before = ok (.InvalidInstructionData,after) ∧
      accounts after = accounts before := by
  constructor
  · rw [NBG_Error.transition,returned]
  · exact logFrame _ _ _ returned
/-- Every successful return of this wrapper is a rejection value. Failure or
nonreturn cannot become acceptance via this helper. -/
theorem rejects {State : Type} (log : String → State → Result State)
    (error : NBG_Error.E) (before after : State) (value : NBG_Error.P)
    (returned : NBG_Error.run log error before = ok (value,after)) :
    value = .InvalidInstructionData := by
  rw [NBG_Error.transition] at returned
  cases h : log (NBG_Error.message error) before <;> simp [h] at returned
  exact returned.1.symm
#print axioms frame
#print axioms rejects
end NBQ_ErrorControl
