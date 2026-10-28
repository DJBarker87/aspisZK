import PV_L2C_HonestHelper
set_option autoImplicit false
noncomputable section
namespace PV_L2C_HonestValidity
open R1Z R0P R0Z.ZkStatement R0Z.HonestValidity PV_L2C_HonestCaller
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Every decoded native compiler trace is honestly valid on the existing
NoPole domain. This does not prove the native inverse implementation or
remove the existing pole event. -/
theorem valid (F : Subfield K) (B : PackBasis F)
    (i : PV_L2C_HonestCaller.Family (K:=K)) (ch : R0Z.HonestView.Challenges K)
    (hnp : NoPole ((source (K:=K)).build i) (ch.sem 0) (ch.sem 1)) :
    R0Z.HonestValid.HonestValid ((source (K:=K)).public i) B ((source (K:=K)).build i) ch := by
  exact honestValid_of _ B _ ch (builder_sound F B (((source (K:=K)).public i),()) i rfl) hnp
#print axioms valid
end PV_L2C_HonestValidity
