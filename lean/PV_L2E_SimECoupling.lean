import PV_L2E_LawPermutation
import R1Z.SimulatorR1
set_option autoImplicit false
noncomputable section
namespace PV_L2E_SimECoupling
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsGood R0Z.HvzkV R0Z.HvzkS
  R0Z.RefPayload R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1
  R1Z.SimulatorR1
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
  (hs : R0Z.HonestValidity.BuilderSoundOn h B x)

/-- The simulator is the ACTUAL simE. The relabelling is proof-side only;
it changes no source, simulator, observer or charged event. -/
def tapePermutation (w : h.Instance) (ch : Challenges K)
    (hP : P_R1 h.transport B hB ch) (hV : VR1 h ch w) (hw : h.public w=x.1) :
    Tape K F ≃ Tape K F :=
  PV_L2E_LawPermutation.permutation
    (view (Bat := R1Bat) h B outputs x w ch) (simE (Bat := R1Bat) h.transport B outputs x ch)
    (hvzk_R1S h B hB outputs x hpub hs w ch hP hV hw)

theorem actual_simE_pointwise (w : h.Instance) (ch : Challenges K)
    (hP : P_R1 h.transport B hB ch) (hV : VR1 h ch w) (hw : h.public w=x.1)
    (t : Tape K F) :
    simE (Bat := R1Bat) h.transport B outputs x ch
      (tapePermutation h B hB outputs x hpub hs w ch hP hV hw t) =
        view (Bat := R1Bat) h B outputs x w ch t :=
  PV_L2E_LawPermutation.pointwise _ _ _ t

/-- Any function of the ENTIRE fixed coin vector can be retained jointly,
including eager unused blocks and rejected-attempt histories. This law does
not bind that function to native trace producers. -/
include hpub hs in
theorem full_coins_joint {C O : Type} (c : C) (observeCoins : C → O)
    (w : h.Instance) (ch : Challenges K)
    (hP : P_R1 h.transport B hB ch) (hV : VR1 h ch w) (hw : h.public w=x.1)
    (test : O × View K CommitHandle Aux R1Bat → ℚ) :
    mean (fun t : Tape K F => test (observeCoins c,view (Bat := R1Bat) h B outputs x w ch t)) =
    mean (fun t : Tape K F => test (observeCoins c,simE (Bat := R1Bat) h.transport B outputs x ch t)) := by
  exact R0Z.LawTransport.mean_eq_of_equalLaws _ _
    (fun v => test (observeCoins c,v))
    (hvzk_R1S h B hB outputs x hpub hs w ch hP hV hw)

#print axioms tapePermutation
#print axioms actual_simE_pointwise
#print axioms full_coins_joint
end PV_L2E_SimECoupling
