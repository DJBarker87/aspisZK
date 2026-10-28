import R1Z.PV_RunJoin_ConsumerBoundary25
import R1Z.PV_Src_Consumer
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ConsumerUse25
open R0P R0Z.ZkStatement R0Z.HonestValidity PV_RunJoin_ConsumerBoundary25
local notation "K" => PrivacyR1AcctBasis.K
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

/-- Choose the public fibre occupied by the non-honest native singleton. -/
def x : Statement K Unit := ((source (K := K)).public (), ())

theorem matching_public : (source (K := K)).public () = x.1 := rfl
#print axioms matching_public

/-- Existing generic consumers are instantiated, with their existing types,
on the genuine certificate from ConsumerBoundary25. No vacuous premise. -/
theorem protocol_join : BuilderProtocolInstance.RustBuilderJoin (source (K := K)) x :=
  BuilderProtocolInstance.join_of_identification _ _ target identification
#print axioms protocol_join

theorem protocol_join_at_nonhonest :
    (∃ p : BuilderCanonical.Instance (K := K),
      BuilderSource.prover.public p = x.1 ∧
      (source (K := K)).build () = BuilderSource.prover.build p) ∧
    ¬ HonestInput (K := K) (inputs ()) :=
  ⟨protocol_join () matching_public,not_honest⟩
#print axioms protocol_join_at_nonhonest

theorem source_sound {F : Subfield K} (B : PackBasis F) :
    BuilderSoundOn (source (K := K)) B x :=
  BuilderSource.builder_refinement_D46_D51 BuilderProtocolInstance.field_large
    F B x _ target identification
#print axioms source_sound

theorem consumer {F : Subfield K} (B : PackBasis F) :
    PrivacyR1Headline.BuilderPremises (source (K := K)) B x :=
  PV_Src_Consumer.of_identification B x _ target identification
#print axioms consumer

/-- The actual public-fibre consumer returns its conclusions at w=(),
whose cached full payload provably is not the successful compiler return. -/
theorem consumer_at_nonhonest {F : Subfield K} (B : PackBasis F) :
    (R0Z.ZkStatement.PublicBase F x.1 ∧ BuilderSoundOn (source (K := K)) B x) ∧
    ¬ HonestInput (K := K) (inputs ()) :=
  ⟨consumer B () matching_public,not_honest⟩
#print axioms consumer_at_nonhonest

/-- The matching-public guard cannot supply the missing honesty fact. -/
theorem matching_fibre_not_honest :
    ¬ (∀ w : (source (K := K)).Instance,
      (source (K := K)).public w = x.1 → HonestInput (K := K) (inputs w)) := by
  intro h
  exact not_honest (h () matching_public)
#print axioms matching_fibre_not_honest
end R1Z.PV_RunJoin_ConsumerUse25
