import NDO_JHa_CurrentRho
import RPt_JFq_State
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_ImmutableState
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
open AspisV8R19.SqueezeOracleBridge

theorem bytes : encodeState JGg_Opening32.next0=JFq_State.value := by
  apply Subtype.ext
  rfl
#print axioms bytes

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    p.state=JFq_State.value :=
  (JHa_CurrentRho.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare).2.2.trans bytes
#print axioms source
end AspisR1.JHe_ImmutableState
end
