import R1Z.PV_L2_F3Absorption
import R1Z.PV_L2_F3EntropyPrefix

/-! Ideal E1-coordinate composition: the entire unchanged entropy return/state
is retained jointly with scalar counts and simE. This is not the full L1 Run,
ROM-programming join or failed scalar-prefix observation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3EntropyJoin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbortBounds R0Z.HvzkV R0Z.RefPayload
  R1Z.Batched R1Z.MaskImageVR1 R1Z.PredicateR1 R1Z.SimulatorR1
  R1Z.ProverCommitWordCarrier R1Z.ProverCommitSourceDecoder
  R1Z.PV_L2_F3Tape R1Z.PV_L2_F3Absorption R1Z.PV_L2_F3EntropyPrefix
  R1Z.ProverCommitPublicNonce40 R1Z.ProverCommitLedger36
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)
theorem entropy_count_absorption (h : HonestProver K) (basis : PackBasis (sourceBase (K := K)))
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (ch : Challenges K) (hB : R0Z.K4.PackField basis)
    (hpub : PublicBase F x.1) (hs : R0Z.HonestValidity.BuilderSoundOn h basis x)
    (hP : P_R1 h.transport basis hB ch) (hV : VR1 h ch w) (hw : h.public w=x.1)
    (nonce : Path) (schedule : Schedule) (state : State)
    (test : (Except EntropyError Private × State) →
      Option (View K CommitHandle Aux R1Bat × History) → ℚ) :
    mean (fun seeds : Seeds => mean (fun p : Inputs × Tape K F =>
      test (generate nonce schedule (extend seeds) state)
        (sourceView h basis outputs x w ch p.1 p.2))) =
    mean (fun seeds : Seeds => mean (fun p : Inputs × Tape K F =>
      test (generate nonce schedule (extend seeds) state)
        (simView h basis outputs x ch p.1 p.2))) := by
  apply congrArg mean
  funext seeds
  exact source_count_absorption h basis outputs x w ch hB hpub hs hP hV hw
    (test (generate nonce schedule (extend seeds) state))

#print axioms entropy_count_absorption
end R1Z.PV_L2_F3EntropyJoin
