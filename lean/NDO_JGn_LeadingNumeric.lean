import NDO_JGl_LeadingMath
import NDO_JGl_WordProof
import NDO_JGj_LeadingTotal
import RPv_FJe_PackedValues
import NDO_JGl_NumericCanonical
import NDO_JGl_ArrayIdentity
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_LeadingNumeric
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
theorem pack : (fun g=>R0P.poseidonPackingFormula iBasis uBasis
    (fun j=>decoded JGl_VectorData.leading (FJe_ExternalAdjoint.lane g j)))=decoded JGl_NumericData.leading := by
  funext g
  fin_cases g <;> jgl_words
#print axioms pack

theorem source : state_only_poseidon.leading_pair_packed JGl_NumericData.openings=ok JGl_NumericData.leading := by
  obtain ⟨out,run,canon⟩ := JGj_LeadingTotal.source JGl_NumericData.openings JGl_NumericCanonical.a JGl_NumericCanonical.c
  have val := FJe_PackedValues.leading JGl_NumericData.openings out JGl_NumericCanonical.a JGl_NumericCanonical.c run
  have meaning : decoded out=decoded JGl_NumericData.leading := by
    erw [val.2,JGl_LeadingMath.value]
    exact pack
  have same := JGl_ArrayIdentity.value out JGl_NumericData.leading canon JGl_NumericCanonical.leading meaning
  rw [same] at run
  exact run
#print axioms source
end AspisR1.JGn_LeadingNumeric
end
