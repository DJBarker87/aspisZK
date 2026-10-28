import NDO_JGl_InternalLane0
import NDO_JGl_InternalRestA
import NDO_JGl_InternalRestB
import NDO_JGl_InternalPairTotal
import NDO_JGl_NumericCanonical
import NDO_JGl_ArrayIdentity
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_InternalNumeric
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
theorem model : R0P.poseidonInterpolatedInternalPair (decoded JGl_NumericData.a)
    (decoded JGl_NumericData.low)=decoded JGl_NumericData.internal := by
  funext i
  fin_cases i
  · exact JGl_InternalLane0.lane0
  · exact JGl_InternalRestA.lane1
  · exact JGl_InternalRestA.lane2
  · exact JGl_InternalRestA.lane3
  · exact JGl_InternalRestA.lane4
  · exact JGl_InternalRestA.lane5
  · exact JGl_InternalRestA.lane6
  · exact JGl_InternalRestA.lane7
  · exact JGl_InternalRestA.lane8
  · exact JGl_InternalRestB.lane9
  · exact JGl_InternalRestB.lane10
  · exact JGl_InternalRestB.lane11
  · exact JGl_InternalRestB.lane12
  · exact JGl_InternalRestB.lane13
  · exact JGl_InternalRestB.lane14
  · exact JGl_InternalRestB.lane15
#print axioms model

theorem source : state_only_poseidon.interpolated_internal_pair JGl_NumericData.a JGl_NumericData.low=
    ok JGl_NumericData.internal := by
  obtain ⟨out,run,canon,val⟩ := JGl_InternalPairTotal.source JGl_NumericData.a JGl_NumericData.low
    JGl_NumericCanonical.a JGl_NumericCanonical.low
  have same := JGl_ArrayIdentity.value out JGl_NumericData.internal canon JGl_NumericCanonical.internal (val.trans model)
  rw [same] at run
  exact run
#print axioms source
end AspisR1.JGl_InternalNumeric
end
