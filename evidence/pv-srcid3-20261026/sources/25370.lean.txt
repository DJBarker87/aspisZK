import R1Z.PV_Src_SelectedThree
import R1Z.PV_Src_NativeConsumer

/-! The unchanged BuilderPremises consumer accepts the three-field instance.
All reference dictionaries remain explicit; no deployed RunJoin is installed. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_ThreeConsumer
open R0P R0Z.ZkStatement BuilderForestAdmissionPort
local notation "K" => PrivacyR1AcctBasis.K
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P
local instance : ExternalLinear := PV_Src_FrozenInput.external
local instance : Records := PV_Src_FrozenInput.records

theorem builder_premises {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (x : Statement K CommitHandle)
    {I : Type} {selected : I → PV_Src_FrozenInput.Data («K» := K)}
    {transport : Fin 1024 ≃ Fin 1024}
    (p : PV_Src_SelectedThree.Remainder («K» := K) selected transport) :
    PrivacyR1Headline.BuilderPremises
      (PV_Src_NativeIdentification.prover (fun i => PV_Src_FrozenInput.input (selected i)) transport) B x :=
  PV_Src_NativeConsumer.builder_premises B x (PV_Src_SelectedThree.complete p)

#print axioms builder_premises
end R1Z.PV_Src_ThreeConsumer
