import R1Z.PV_Src_NativeIdentification
import R1Z.PV_Src_Consumer

/-! The unchanged headline BuilderPremises contract accepts the constructed
certificate for actual returned compiler columns. Remaining primitive native
facts stay explicit. This does not install a deployed FS execution or RunJoin. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_NativeConsumer
open R0P R0Z.ZkStatement
open BuilderForestAdmissionPort
local notation "K" => PrivacyR1AcctBasis.K
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P
variable [ExternalLinear] [Records]
variable {I : Type} {inputs : I → PV_Src_NativeInput.Input}
  {transport : Fin 1024 ≃ Fin 1024}

theorem builder_premises {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle)
    (p : PV_Src_NativeIdentification.PV_Src_Premises («K» := K) inputs transport) :
    PrivacyR1Headline.BuilderPremises
      (PV_Src_NativeIdentification.prover inputs transport) B x :=
  PV_Src_Consumer.of_identification B x _ _ (PV_Src_NativeIdentification.identification p)

theorem phased_builder_premises {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle)
    (p : PV_Src_NativeIdentification.PV_Src_Premises («K» := K) inputs transport) :
    PrivacyR1Headline.BuilderPremises
      (PhaseWireLog2Bin.honest (PV_Src_NativeIdentification.prover inputs transport)) B x := by
  change PrivacyR1Headline.BuilderPremises
    (PV_Src_NativeIdentification.prover inputs transport) B x
  exact builder_premises B x p

#print axioms builder_premises
#print axioms phased_builder_premises
end R1Z.PV_Src_NativeConsumer
