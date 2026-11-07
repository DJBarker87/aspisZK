import LIB_VRounds
import LIB_VClaims
import LIB_VCircle
import LIB_VTerminal
import LIB_VDomains
set_option autoImplicit false
namespace LIB_VSemantic
abbrev semanticRounds := LIB_VRounds.semanticRounds
abbrev claims := LIB_VClaims.claims
abbrev circle := LIB_VCircle.circle
abbrev terminalQm31 := LIB_VTerminal.terminalQm31
abbrev publicDom := LIB_VDomains.publicDom
abbrev finishInputDom := LIB_VDomains.finishInputDom
theorem ready : RSL.Child.Functional semanticRounds ∧ RSL.Child.Functional claims ∧
 RSL.Child.Functional circle ∧ RSL.Child.Functional terminalQm31 :=
 ⟨LIB_VRounds.functional,LIB_VClaims.functional,LIB_VCircle.functional,LIB_VTerminal.functional⟩
#print axioms ready
end LIB_VSemantic
