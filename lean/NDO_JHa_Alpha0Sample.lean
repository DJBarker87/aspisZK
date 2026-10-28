import NDO_JHa_OrdinaryValue
import NDO_JGg_Opening29
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Alpha0Sample
open Aeneas Aeneas.Std Result AspisR1ClaimPreparedBridge
open AspisV8R19.SqueezeOracleBridge
abbrev target := FIo_Install.toE JFq_Alpha0.scalar

theorem canonical : FIo_WideValues.Canon target := by
  change ((492967452<2147483647 ∧ 709301790<2147483647) ∧ (1617612614<2147483647 ∧ 599334322<2147483647)) ∧ ((1668486716<2147483647 ∧ 1253062525<2147483647) ∧ (341779229<2147483647 ∧ 880523595<2147483647))
  omega
#print axioms canonical

theorem value : AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide target)=
    R0C.ModuloField.ordinary (decodeState (encodeState JGg_Opening29.block0)) := by
  with_unfolding_all rfl
#print axioms value

theorem sample : AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic
    (encodeState JGg_Opening29.block0)=ok (JHa_OrdinaryValue.fromNative target) := by
  obtain ⟨out,call⟩ := JGg_OrdinaryTotal.source (encodeState JGg_Opening29.block0)
  rw [JHa_OrdinaryValue.identify _ target canonical value out call] at call
  exact call
#print axioms sample
end AspisR1.JHa_Alpha0Sample
end
