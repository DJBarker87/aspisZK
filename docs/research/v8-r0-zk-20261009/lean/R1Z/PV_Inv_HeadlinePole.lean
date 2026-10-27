import R1Z.PV_Inv_RegistryZeroEvent
import R1Z.MaskImageVR1
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_HeadlinePole
open R0P R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV
open PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference PV_Inv_GlobalSlots PV_Inv_GlobalSafety
variable {K CommitHandle Aux Bat Adv W : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [Zero W] [DecidableEq W]

theorem attempt_contained (P : Challenges K → Prop) (h : HonestProver K)
    (ab : AbortBridge K CommitHandle Aux Bat Adv) (adv : Adv) (x : Statement K CommitHandle)
    (w : h.Instance) (coin : ab.Coins)
    (banks : Banks K) (join : P_banks banks (h.build w))
    (weight : SourceLink K → W) (registry : List (SourceLink K)) (enumeration : P_registry registry)
    (s : State Key K W)
    (run : PV_Inv_GlobalSlots.run (empty 0)
      (entries banks ((ab.draw adv x coin).sem 0) weight registry)=some s)
    (public_guard : P (ab.draw adv x coin))
    (zero : PV_Inv_RegistryZeroEvent.zeroEvent ((ab.draw adv x coin).sem 1) s) :
    attemptBad P h (MaskImageVR1.VR1 h) ab adv x w coin := by
  refine ⟨public_guard,?_⟩
  exact PV_Inv_RegistryZeroEvent.contained banks (h.build w) join _ _ weight registry enumeration s run zero

#print axioms attempt_contained
end R1Z.PV_Inv_HeadlinePole
