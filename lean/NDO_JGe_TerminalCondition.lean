import NDO_JGd_MaskedGate
import RPu_FIq_Terminal
set_option autoImplicit false
namespace AspisR1.JGe_TerminalCondition
open Aeneas Aeneas.Std Result

/-- The single unresolved source-call identification at the real terminal gate.
This proposition is deliberately not asserted as inhabited. -/
def Identified : Prop :=
  FIq_Terminal.terminal JFs_PublicSerialization.value JFu_ClaimsData.claims
    JFm_PartialAlpha.a10 JFm_Begin.challenges=ok (.Ok JGd_NumericData.neededTerminal)

theorem gate (identified : Identified) :
    ∃ terminal,
      FIq_Terminal.terminal JFs_PublicSerialization.value JFu_ClaimsData.claims
        JFm_PartialAlpha.a10 JFm_Begin.challenges=ok (.Ok terminal) ∧
      JGb_MaskedArithmetic.run terminal JGd_NumericData.mask=ok JGd_NumericData.running :=
  ⟨JGd_NumericData.neededTerminal,identified,JGd_MaskedGate.source⟩
#print axioms gate
end AspisR1.JGe_TerminalCondition
