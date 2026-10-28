import NDO_JGl_Semantic00
import NDO_JGl_Semantic01
import NDO_JGl_Semantic02
import NDO_JGl_Semantic03
import NDO_JGl_Semantic04
import NDO_JGl_Semantic05
import NDO_JGl_Semantic06
import NDO_JGl_Semantic07
import NDO_JGl_Semantic08
import NDO_JGl_Semantic09
import NDO_JGl_Semantic10
import NDO_JGl_Semantic11
import NDO_JGl_Semantic12
import NDO_JGl_SemanticRestA
import NDO_JGl_SemanticRestC
import NDO_JGl_ArrayIdentity
import NDO_JGl_NumericCanonical
import NDO_JFy_SemanticValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_SemanticNumeric
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)

theorem model : FIy_NativeCoefficients.model JFu_PublicSemantic.value
    JGl_NumericData.openings JGl_NumericData.selectors=decoded JGl_NumericData.semantic := by
  funext i
  fin_cases i
  · exact JGl_Semantic00.value
  · exact JGl_Semantic01.value
  · exact JGl_Semantic02.value
  · exact JGl_Semantic03.value
  · exact JGl_Semantic04.value
  · exact JGl_Semantic05.value
  · exact JGl_Semantic06.value
  · exact JGl_Semantic07.value
  · exact JGl_Semantic08.value
  · exact JGl_Semantic09.value
  · exact JGl_Semantic10.value
  · exact JGl_Semantic11.value
  · exact JGl_Semantic12.value
  · exact JGl_Semantic13.value
  · exact JGl_Semantic14.value
  · exact JGl_Semantic15.value
  · exact JGl_Semantic16.value
  · exact JGl_Semantic17.value
  · exact JGl_Semantic18.value
  · exact JGl_Semantic19.value
  · exact JGl_Semantic20.value
  · exact JGl_Semantic21.value
  · exact JGl_Semantic22.value
  · exact JGl_Semantic23.value
#print axioms model

theorem source (out : Array field.QM31 24#usize)
    (run : pool_v1.pair_forest_semantic_terminal.semantic_packed JFu_PublicSemantic.value
      JGl_NumericData.openings JGl_NumericData.selectors=ok out) :
    out=JGl_NumericData.semantic := by
  have h := JFy_SemanticValue.value JGl_NumericData.a JGl_NumericData.b JGl_NumericData.c
    JGl_NumericData.selectors out JGl_NumericCanonical.a JGl_NumericCanonical.b JGl_NumericCanonical.c
    JGl_NumericCanonical.high JGl_NumericCanonical.low run
  exact JGl_ArrayIdentity.value out JGl_NumericData.semantic h.1 JGl_NumericCanonical.semantic (h.2.trans model)
#print axioms source
end AspisR1.JGl_SemanticNumeric
end
