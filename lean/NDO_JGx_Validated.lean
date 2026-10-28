import NDO_JGx_RealStatement
import NDO_JGx_AdapterEncoder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Validated
open Aeneas Aeneas.Std Result DrvC_Installation

def value : AdapterRw.r1_pool_adapter.ValidatedAsqa := ⟨JGx_RealStatement.value,57607#usize⟩

theorem proofLength : value.proof_length=57607#usize := rfl
#print axioms proofLength

theorem encoder {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (DrvC_Installation.sdk (JGx_Configuration.value c err)).op22 value.statement=ok (.Ok JGx_PublicArray.value) := by
  rw [JGx_AdapterEncoder.source]
  exact JGx_RealStatement.encode
#print axioms encoder
end AspisR1.JGx_Validated
end
