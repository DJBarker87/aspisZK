import R1Z.PV_RunJoin_HonestIdentification26
import R1Z.PV_Src_Consumer
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_HonestConsumer26
open R0P R0Z.ZkStatement R0Z.HonestValidity PV_RunJoin_HonestIdentification26
local notation "K" => PrivacyR1AcctBasis.K
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

/-- The original source consumer, at every statement and every supplied basis. -/
theorem consumer {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle) :
    PrivacyR1Headline.BuilderPremises (source_honest («K» := K)) B x :=
  PV_Src_Consumer.of_identification B x _ target identification
#print axioms consumer

/-- The D46-D51 builder obligation has no remaining source-identification premise. -/
theorem source_sound {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle) :
    BuilderSoundOn (source_honest («K» := K)) B x :=
  BuilderSource.builder_refinement_D46_D51 BuilderProtocolInstance.field_large
    F B x _ target identification
#print axioms source_sound

/-- Existing protocol join, with the same matching-public guard. -/
theorem protocol_join {CommitHandle : Type} (x : Statement K CommitHandle) :
    BuilderProtocolInstance.RustBuilderJoin (source_honest («K» := K)) x :=
  BuilderProtocolInstance.join_of_identification _ x target identification
#print axioms protocol_join

/-- The other existing soundness route consumes that same protocol join. -/
theorem sound_of_join {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle) :
    BuilderSoundOn (source_honest («K» := K)) B x :=
  BuilderProtocolInstance.builder_sound_of_join B x _ (protocol_join x)
#print axioms sound_of_join

/-- All honest inputs on any public fibre, not just the saved fixtures. -/
theorem at_honest_input {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle)
    (i : Honest («K» := K)) (hi : source_honest.public i = x.1) :
    PublicBase F x.1 ∧ BuilderSoundOn (source_honest («K» := K)) B x :=
  consumer B x i hi
#print axioms at_honest_input

/-- The exact canonical witness supplied by the honest-input handoff. -/
theorem canonical_fibre {CommitHandle : Type} (x : Statement K CommitHandle)
    (i : Honest («K» := K)) (hi : source_honest.public i = x.1) :
    BuilderSource.prover.public (target i) = x.1 ∧
      source_honest.build i = BuilderSource.prover.build (target i) :=
  ⟨(public_eq i).symm.trans hi, build_eq i⟩
#print axioms canonical_fibre
end R1Z.PV_RunJoin_HonestConsumer26
