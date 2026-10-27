import R1Z.PV_L2_F5Transport
import R1Z.SimulatorR1

/-! The raw QueryScan history is fixed by middle coins, so the existing
witness absorption theorem transports it jointly with the view, for each
fixed coin vector and reached valid challenge. This is the actual simE.
This does not assert native L1/L2 execution refinement or an ideal-ROM join. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F5Absorption
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbortBounds R0Z.HvzkV R0Z.HvzkS
  R0Z.RefPayload R1Z.GamesR1 R1Z.Batched R1Z.PredicateR1 R1Z.PoleMassR1
  R1Z.MaskImageVR1 R1Z.SimulatorR1 R1Z.PV_L2_F5Transport
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (h : HonestProver K) (B : PackBasis F)
  (hB : R0Z.K4.PackField B)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
  (hs : R0Z.HonestValidity.BuilderSoundOn h B x)

include hpub hs in
/-- A test can inspect ALL attempts' raw parser histories together with the
selected view. Nothing is independently resampled or replaced by query sets. -/
theorem fixed_coins_joint (N : Nat) (coins : Fin N → R1Coins W.Cm W.Tab)
    (k : Fin N) (w : h.Instance)
    (hP : P_R1 h.transport B hB (drawW W (coins k)))
    (hV : VR1 h (drawW W (coins k)) w) (hw : h.public w = x.1)
    (test : ((Fin N → _) × View K CommitHandle Aux R1Bat) → ℚ) :
    mean (fun t : Tape K F => test
      ((fun j => coinHistory W (coins j)), view h B outputs x w (drawW W (coins k)) t)) =
    mean (fun t : Tape K F => test
      ((fun j => coinHistory W (coins j)), simE h.transport B outputs x (drawW W (coins k)) t)) := by
  have hv := hvzk_R1S h B hB outputs x hpub hs w (drawW W (coins k)) hP hV hw
  exact LawTransport.mean_eq_of_equalLaws _ _
    (fun v => test ((fun j => coinHistory W (coins j)), v)) hv

#print axioms fixed_coins_joint
end R1Z.PV_L2_F5Absorption
