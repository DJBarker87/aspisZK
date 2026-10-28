import NDO_JGn_FullMath
import NDO_JGl_WordProof
import NDO_JGj_FullTotal
import RPv_FJe_PackedValues
import NDO_JGl_NumericCanonical
import NDO_JGl_ArrayIdentity
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_FullNumeric
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
theorem pack : (fun g=>R0P.poseidonPackingFormula iBasis uBasis
    (fun j=>decoded JGl_VectorData.full (FJe_ExternalAdjoint.lane g j)))=decoded JGl_NumericData.full := by
  funext g
  fin_cases g <;> jgl_words
#print axioms pack

theorem source : state_only_poseidon.interpolated_full_pair_packed JGl_NumericData.a JGl_NumericData.low=ok JGl_NumericData.full := by
  obtain ⟨out,run,canon⟩ := JGj_FullTotal.source JGl_NumericData.a JGl_NumericData.low JGl_NumericCanonical.a JGl_NumericCanonical.low
  have val := FJe_PackedValues.full JGl_NumericData.a JGl_NumericData.low out JGl_NumericCanonical.a JGl_NumericCanonical.low run
  have meaning : decoded out=decoded JGl_NumericData.full := by
    erw [val.2,JGn_FullMath.value]
    exact pack
  have same := JGl_ArrayIdentity.value out JGl_NumericData.full canon JGl_NumericCanonical.full meaning
  rw [same] at run
  exact run
#print axioms source
end AspisR1.JGn_FullNumeric
end
