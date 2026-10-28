import PV_L2C_HonestCaller
set_option autoImplicit false
noncomputable section
namespace PV_L2C_HonestHelper
open R1Z R0P R0Z.ZkStatement R0Z.HonestValidity PV_L2C_HonestCaller
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- The decoded honest compiler trace has balanced helper values at every
challenge, with no helper-sum assumption. Native materialization is separate. -/
theorem total (F : Subfield K) (B : PackBasis F) (i : PV_L2C_HonestCaller.Family (K:=K)) (lam chi : K) :
    (∑ r, R0Z.HonestView.helper ((source (K:=K)).public i)
      ((source (K:=K)).build i) lam chi r)=0 := by
  have hs := builder_sound F B (((source (K:=K)).public i),()) i rfl
  exact hs.helperSum lam chi
#print axioms total

theorem inactive (F : Subfield K) (B : PackBasis F) (i : PV_L2C_HonestCaller.Family (K:=K)) (lam chi : K) :
    (∑ r ∈ R0P.copyInactiveRows, R0Z.HonestView.helper ((source (K:=K)).public i)
      ((source (K:=K)).build i) lam chi r)=0 := by
  have hs := builder_sound F B (((source (K:=K)).public i),()) i rfl
  exact hs.helperInactive lam chi
#print axioms inactive
end PV_L2C_HonestHelper
