import NHD_ErrorLabels
set_option autoImplicit false
noncomputable section
namespace NHY_ErrorFragments
open Aeneas Aeneas.Std Result
abbrev E := NGL_ErrorModel.E
abbrev PE := NGL_ErrorModel.PE
/-- Compiler MIR of Error::fmt selects one label and makes one write_str call.
The format literal contributes its prefix before that callback. -/
def fragments (e : E) : List String := ["r1:error:",NGL_ErrorModel.label e]
def render (e : E) : String := String.join (fragments e)

theorem ordered_message (e : E) : render e = NGL_ErrorModel.message e := by
  cases e <;> rfl

theorem syscall_bytes (e : E) :
    (render e).toUTF8 = (NGL_ErrorModel.message e).toUTF8 :=
  congrArg String.toUTF8 (ordered_message e)

/-- Already-proved finite message table is reused, not recreated. -/
theorem table (e : E) : (e,render e) ∈ NHD_ErrorLabels.casesTable := by
  rw [ordered_message]
  exact NHD_ErrorLabels.exhaustive e

/-- Exact full Result plus ordered logger state. No premise asserts that the
formatter succeeds, and a failing/diverging syscall is not converted to Ok. -/
theorem logger {S : Type} (log : String → S → Result S) (e : E) (s : S) :
    (do let after ← log (render e) s
        ok (AdapterRw.solana_program_error.ProgramError.InvalidInstructionData,after)) = NGL_ErrorModel.run log e s := by
  rw [ordered_message]
  rfl
#print axioms ordered_message
#print axioms syscall_bytes
#print axioms table
#print axioms logger
end NHY_ErrorFragments
