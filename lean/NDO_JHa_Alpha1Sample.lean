import NDO_JHa_OrdinaryValue
import NDO_JGg_Opening30
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Alpha1Sample
open Aeneas Aeneas.Std Result AspisR1ClaimPreparedBridge
open AspisV8R19.SqueezeOracleBridge
abbrev target := FIo_Install.toE JFq_Alpha1.scalar

theorem canonical : FIo_WideValues.Canon target := by
  change ((1923325677<2147483647 ∧ 606708475<2147483647) ∧ (390399940<2147483647 ∧ 1424274113<2147483647)) ∧ ((1600018693<2147483647 ∧ 561365806<2147483647) ∧ (1230057896<2147483647 ∧ 509172918<2147483647))
  omega
#print axioms canonical

theorem value : AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide target)=
    R0C.ModuloField.ordinary (decodeState (encodeState JGg_Opening30.block0)) := by
  with_unfolding_all rfl
#print axioms value

theorem sample : AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic
    (encodeState JGg_Opening30.block0)=ok (JHa_OrdinaryValue.fromNative target) := by
  obtain ⟨out,call⟩ := JGg_OrdinaryTotal.source (encodeState JGg_Opening30.block0)
  rw [JHa_OrdinaryValue.identify _ target canonical value out call] at call
  exact call
#print axioms sample
end AspisR1.JHa_Alpha1Sample
end
