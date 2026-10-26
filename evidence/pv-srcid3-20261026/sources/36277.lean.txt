import R1Z.PV_Src_Canonical
import R1Z.PV_Src_ForestCanonical
import R1Z.ProverCommitAdmittedEndpoint

/-! The original BuilderPremises consumer accepts the constructed extracted
stage certificate. The fixed deployed endpoint still selects its canonical
input; this theorem does not install a new deployed execution or RunJoin. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_Consumer
open R0P R0Z.ZkStatement R0Z.HonestValidity
local notation "K" => PrivacyR1AcctBasis.K
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

/-- No change to the consumer's quantifiers, matching-public guard or four
soundness conclusions. The map's admission proof remains an explicit input. -/
theorem of_identification {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle) (source : HonestProver K)
    (toInstance : source.Instance → BuilderCanonical.Instance («K» := K))
    (identification : BuilderSource.SourceIdentification source toInstance) :
    PrivacyR1Headline.BuilderPremises source B x := by
  intro w hw
  constructor
  · rw [← hw, identification.public_eq w]
    exact BuilderCanonical.publicBase_map F _
  · exact BuilderSource.builder_refinement_D46_D51
      BuilderProtocolInstance.field_large F B x source toInstance identification

theorem extracted_stages {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle) :
    PrivacyR1Headline.BuilderPremises
      (PV_Src_Identification.prover (PV_Src_Canonical.inputs («K» := K)) PV_Src_Transport.transport) B x :=
  of_identification B x _ _ PV_Src_Canonical.identification

theorem forest_stages {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle) :
    PrivacyR1Headline.BuilderPremises
      (PV_Src_ForestIdentification.prover (PV_Src_ForestCanonical.inputs («K» := K)) PV_Src_Transport.transport) B x :=
  of_identification B x _ _ PV_Src_ForestCanonical.identification

/-- This is the existing endpoint contract, reused without changing its
statement. It does not consume SourceIdentification as an argument. -/
theorem existing_consumer {CommitHandle : Type}
    (x : Statement K CommitHandle) :
    PrivacyR1Headline.BuilderPremises
      (PhaseWireLog2Bin.honest (BuilderSource.prover («K» := K)))
      PrivacyR1AcctBasis.basis x := by
  change PrivacyR1Headline.BuilderPremises
    (BuilderSource.prover («K» := K)) PrivacyR1AcctBasis.basis x
  exact PrivacyR1Headline.builder_premises_canonical _ _

#print axioms of_identification
#print axioms extracted_stages
#print axioms forest_stages
#print axioms existing_consumer
end R1Z.PV_Src_Consumer
