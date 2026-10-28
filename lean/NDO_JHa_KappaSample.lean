import NDO_JHa_OrdinaryValue
import NDO_JGg_Opening28
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_KappaSample
open Aeneas Aeneas.Std Result AspisR1ClaimPreparedBridge
open AspisV8R19.SqueezeOracleBridge
abbrev target := FIo_Install.toE JFq_Kappa.scalar

theorem canonical : FIo_WideValues.Canon target := by
  change ((1116662073<2147483647 ∧ 1579954339<2147483647) ∧ (1176243488<2147483647 ∧ 728698552<2147483647)) ∧ ((640606056<2147483647 ∧ 1197281433<2147483647) ∧ (2141139535<2147483647 ∧ 1224613133<2147483647))
  omega
#print axioms canonical

theorem value : AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide target)=
    R0C.ModuloField.ordinary (decodeState (encodeState JGg_Opening28.block0)) := by
  with_unfolding_all rfl
#print axioms value

theorem sample : AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic
    (encodeState JGg_Opening28.block0)=ok (JHa_OrdinaryValue.fromNative target) := by
  obtain ⟨out,call⟩ := JGg_OrdinaryTotal.source (encodeState JGg_Opening28.block0)
  rw [JHa_OrdinaryValue.identify _ target canonical value out call] at call
  exact call
#print axioms sample
end AspisR1.JHa_KappaSample
end
