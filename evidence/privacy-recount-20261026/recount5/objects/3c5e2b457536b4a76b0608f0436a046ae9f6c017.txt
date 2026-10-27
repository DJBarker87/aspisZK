import R1Z.PV_Inv_GuardAttempt
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_GuardCoupling
open R0P R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV
variable {K CommitHandle Aux Bat Adv S : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- The original coupling projection is an explicit parameter. No new draw or
bad event is introduced. The P conjunct cannot be omitted. -/
theorem reject_contained (P : Challenges K → Prop) (h : HonestProver K)
    (ab : AbortBridge K CommitHandle Aux Bat Adv) (adv : Adv) (x : Statement K CommitHandle)
    (w : h.Instance) (toCoins : S → Fin ab.N → ab.Coins) (u : S) (k : Fin ab.N)
    (hp : P (ab.draw adv x (toCoins u k)))
    (reject : PV_Inv_PreGuard.noPoleRef (h.build w)
      ((ab.draw adv x (toCoins u k)).sem 0) ((ab.draw adv x (toCoins u k)).sem 1) = false) :
    poleBad P h (MaskImageVR1.VR1 h) ab adv x w (toCoins u) :=
  ⟨k,PV_Inv_GuardAttempt.reject_contained P h ab adv x w (toCoins u k) hp reject⟩

theorem clear_off_bad (P : Challenges K → Prop) (h : HonestProver K)
    (ab : AbortBridge K CommitHandle Aux Bat Adv) (adv : Adv) (x : Statement K CommitHandle)
    (w : h.Instance) (toCoins : S → Fin ab.N → ab.Coins) (u : S)
    (outside : ¬ poleBad P h (MaskImageVR1.VR1 h) ab adv x w (toCoins u))
    (k : Fin ab.N) (hp : P (ab.draw adv x (toCoins u k))) :
    PV_Inv_PreGuard.noPoleRef (h.build w)
      ((ab.draw adv x (toCoins u k)).sem 0) ((ab.draw adv x (toCoins u k)).sem 1) = true := by
  cases he : PV_Inv_PreGuard.noPoleRef (h.build w)
    ((ab.draw adv x (toCoins u k)).sem 0) ((ab.draw adv x (toCoins u k)).sem 1) with
  | false => exact False.elim (outside (reject_contained P h ab adv x w toCoins u k hp he))
  | true => rfl

#print axioms reject_contained
#print axioms clear_off_bad
end R1Z.PV_Inv_GuardCoupling
