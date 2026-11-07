import LIB_VParsePrefix
import LIB_VPublicTranscript
import LIB_VBegin
set_option autoImplicit false
namespace LIB_VParse
abbrev parsePrefix := LIB_VParsePrefix.parsePrefix
abbrev semanticBytesDom := LIB_VParsePrefix.semanticBytesDom
abbrev publicTranscript := LIB_VPublicTranscript.publicTranscript
abbrev begin_ := LIB_VBegin.begin_
theorem ready : RSL.Child.Functional parsePrefix ∧
 RSL.Child.Functional publicTranscript ∧ RSL.Child.Functional begin_ :=
 ⟨LIB_VParsePrefix.functional,LIB_VPublicTranscript.functional,LIB_VBegin.functional⟩
#print axioms ready
end LIB_VParse
