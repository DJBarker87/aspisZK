import R1Z.PV_Inv_GuardCoupling
import R1Z.PV_Inv_GuardTraceShape
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_GuardObservedCoupling
open R0P R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV
variable {K CommitHandle Aux Bat Adv S : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- Same original coupling; P-qualified attempts outside existing poleBad have
one fixed Boolean comparison trace. The complete D159 observer still requires
its operand-limb/address/latency refinement. -/
theorem trace_off_bad (P : Challenges K → Prop) (h : HonestProver K)
    (ab : AbortBridge K CommitHandle Aux Bat Adv) (adv : Adv) (x : Statement K CommitHandle)
    (w : h.Instance) (toCoins : S → Fin ab.N → ab.Coins) (u : S)
    (outside : ¬ poleBad P h (MaskImageVR1.VR1 h) ab adv x w (toCoins u))
    (k : Fin ab.N) (hp : P (ab.draw adv x (toCoins u k))) :
    (PV_Inv_ScanCost.recorded ((ab.draw adv x (toCoins u k)).sem 1) true
      (PV_Inv_GuardAllSites.sites (h.build w) ((ab.draw adv x (toCoins u k)).sem 0))).2 =
      List.replicate (PV_Inv_GuardAllSites.active.length * 4) true :=
  PV_Inv_GuardTraceShape.clear_trace (h.build w) _ _
    (PV_Inv_GuardCoupling.clear_off_bad P h ab adv x w toCoins u outside k hp)

#print axioms trace_off_bad
end R1Z.PV_Inv_GuardObservedCoupling
