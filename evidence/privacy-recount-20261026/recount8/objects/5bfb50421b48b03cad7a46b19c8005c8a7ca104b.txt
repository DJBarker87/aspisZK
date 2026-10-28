import R1Z.BuilderSource
import R1Z.PrivacyR1FinalProtocol

/-! The constructed protocol's canonical honest builder. This module proves
model facts, not successful admission by the deployed Rust compiler. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderProtocolInstance
open R0P R0Z.ZkStatement R0Z.HonestValidity
local notation "K" => AspisWideTower.WideExact
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

theorem field_large : 4096 < Fintype.card K := by
  have hc : Fintype.card (ZMod AspisCircleGroupOrder.P) ≤ Fintype.card K :=
    Fintype.card_le_of_injective (algebraMap (ZMod AspisCircleGroupOrder.P) K)
      (RingHom.injective _)
  rw [ZMod.card] at hc
  have hp : AspisCircleGroupOrder.P = 2147483647 := rfl
  rw [hp] at hc
  omega

theorem builder_sound {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle) :
    BuilderSoundOn BuilderSource.prover B x :=
  BuilderSource.builderSoundOn field_large F B x

/-- No transport premise is needed for the four raw-trace soundness fields.
This fibre-local source join is sufficient even when source instances outside
this public fibre have no canonical instance. It is not a Rust certificate. -/
def RustBuilderJoin {CommitHandle : Type} (source : HonestProver K)
    (x : Statement K CommitHandle) : Prop :=
  ∀ w, source.public w = x.1 → ∃ p : BuilderCanonical.Instance («K» := K),
    BuilderSource.prover.public p = x.1 ∧ source.build w = BuilderSource.prover.build p

theorem builder_sound_of_join {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle) (source : HonestProver K)
    (join : RustBuilderJoin source x) : BuilderSoundOn source B x := by
  intro w hw
  obtain ⟨p, hp, ht⟩ := join w hw
  rw [ht]
  exact builder_sound B x p hp

theorem join_of_identification {CommitHandle : Type}
    (source : HonestProver K) (x : Statement K CommitHandle)
    (toInstance : source.Instance → BuilderCanonical.Instance («K» := K))
    (identification : BuilderSource.SourceIdentification source toInstance) :
    RustBuilderJoin source x := by
  intro w hw
  exact ⟨toInstance w, (identification.public_eq w).symm.trans hw,
    identification.build_eq w⟩

#print axioms field_large
#print axioms builder_sound
#print axioms builder_sound_of_join
#print axioms join_of_identification
end R1Z.BuilderProtocolInstance
