import R1Z.PV_Inv_PreGuard
import R1Z.MaskImageVR1
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_GuardAttempt
open R0P R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV
variable {K CommitHandle Aux Bat Adv : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem reject_contained (P : Challenges K → Prop) (h : HonestProver K)
    (ab : AbortBridge K CommitHandle Aux Bat Adv) (adv : Adv) (x : Statement K CommitHandle)
    (w : h.Instance) (coin : ab.Coins) (hp : P (ab.draw adv x coin))
    (reject : PV_Inv_PreGuard.noPoleRef (h.build w)
      ((ab.draw adv x coin).sem 0) ((ab.draw adv x coin).sem 1) = false) :
    attemptBad P h (MaskImageVR1.VR1 h) ab adv x w coin := by
  refine ⟨hp,?_⟩
  intro safe
  have good := (PV_Inv_PreGuard.source_equation (h.build w)
    ((ab.draw adv x coin).sem 0) ((ab.draw adv x coin).sem 1)).mpr safe
  rw [reject] at good
  cases good

#print axioms reject_contained
end R1Z.PV_Inv_GuardAttempt
