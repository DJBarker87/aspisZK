import PV_L2E_SimECoupling
import PV_L2E_TriangularLaw
set_option autoImplicit false
noncomputable section
namespace PV_L2E_GuardedJoint
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsGood R0Z.HvzkV R0Z.HvzkS
  R0Z.RefPayload R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1
  R1Z.SimulatorR1 PV_L2E_SimECoupling
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux C O : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K} [Fintype C]
variable (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
  (hs : R0Z.HonestValidity.BuilderSoundOn h B x)
  (w : h.Instance) (hw : h.public w=x.1)
  (ch : C → Challenges K) (good : C → Prop)
  (hP : ∀ c,good c → P_R1 h.transport B hB (ch c))
  (hV : ∀ c,good c → VR1 h (ch c) w)

/-- The identity outside the original good domain makes a permutation on the
WHOLE sample carrier. No conditional distribution or newly sampled history. -/
def relabel (c : C) : Tape K F ≃ Tape K F :=
  if hg : good c then tapePermutation h B hB outputs x hpub hs w (ch c) (hP c hg) (hV c hg) hw
  else Equiv.refl _

include hpub hs hw hP hV in
/-- Actual simE, jointly with an arbitrary observation of all middle coins.
This is an unconditioned, good-event-weighted equality. Applying it to the
endpoint still requires the same-cp middle-coin law and source trace binding. -/
theorem joint (observe : C → O)
    (test : O × View K CommitHandle Aux R1Bat → ℚ) :
    mean (fun p : C × Tape K F => if good p.1 then
      test (observe p.1,view (Bat := R1Bat) h B outputs x w (ch p.1) p.2) else 0) =
    mean (fun p : C × Tape K F => if good p.1 then
      test (observe p.1,simE (Bat := R1Bat) h.transport B outputs x (ch p.1) p.2) else 0) := by
  let e := relabel h B hB outputs x hpub hs w hw ch good hP hV
  have pointwise :
      (fun p : C × Tape K F => if good p.1 then
        test (observe p.1,view (Bat := R1Bat) h B outputs x w (ch p.1) p.2) else 0) =
      (fun p : C × Tape K F => if good p.1 then
        test (observe p.1,simE (Bat := R1Bat) h.transport B outputs x (ch p.1) (e p.1 p.2)) else 0) := by
    funext p
    by_cases hg : good p.1
    · simp only [if_pos hg,e,relabel,dif_pos hg]
      rw [actual_simE_pointwise]
    · simp only [if_neg hg]
  rw [pointwise]
  exact PV_L2E_TriangularLaw.uniform e
    (fun p : C × Tape K F => if good p.1 then
      test (observe p.1,simE (Bat := R1Bat) h.transport B outputs x (ch p.1) p.2) else 0)

#print axioms relabel
#print axioms joint
end PV_L2E_GuardedJoint
