import NDO_JGl_LeadingAbsorb
import NDO_JGl_LeadingExternal
import NDO_JGl_LeadingPow0
import NDO_JGl_LeadingMid
import NDO_JGl_LeadingPow1
import NDO_JGl_LeadingFinal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_LeadingMath
open FIw_ArrayValue (decoded)
/-- The closed leading mathematical vector, composed from six individually
certified phases instead of expanding the two-round reduction graph. -/
theorem value : R0P.poseidonLeadingPair (decoded JGl_NumericData.a) (decoded JGl_NumericData.c)=
    decoded JGl_VectorData.leading := by
  have ext : R0P.poseidonExternalLinear
      (fun j : Fin 16=>if j.val<8 then decoded JGl_NumericData.a j+decoded JGl_NumericData.c j else decoded JGl_NumericData.a j)=
      decoded JGl_LeadingPhaseData.external :=
    (congrArg R0P.poseidonExternalLinear JGl_LeadingAbsorb.value).trans JGl_LeadingExternal.value
  have first : R0P.poseidonFullRound (decoded JGl_LeadingPhaseData.external) (R0P.poseidonExternalInitial 0)=
      decoded JGl_LeadingPhaseData.mid :=
    (congrArg R0P.poseidonExternalLinear JGl_LeadingPow0.value).trans JGl_LeadingMid.value
  have second : R0P.poseidonFullRound (decoded JGl_LeadingPhaseData.mid) (R0P.poseidonExternalInitial 1)=
      decoded JGl_VectorData.leading :=
    (congrArg R0P.poseidonExternalLinear JGl_LeadingPow1.value).trans JGl_LeadingFinal.value
  have initial := (congrArg (fun state : Fin 16→FIv_NativeValue.K=>
    R0P.poseidonFullRound state (R0P.poseidonExternalInitial 0)) ext).trans first
  exact (congrArg (fun state : Fin 16→FIv_NativeValue.K=>
    R0P.poseidonFullRound state (R0P.poseidonExternalInitial 1)) initial).trans second
#print axioms value
end AspisR1.JGl_LeadingMath
end
