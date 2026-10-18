import R1Z.MaskImageVR1
import R1Z.PoleMassR1
import R1Z.ModelsVR1

/-! J0c item 4 (LOG D40.3, D41): `privacy_R1`, ZK_FS for the retrying R1
prover whose attempts fail at a LogUp pole, with the per-challenge simulator,
error `ε_hit + ε_coll + ε_prog + N · 4096 / Q`.  The couplings come from the
named fields of `R1RealModelV` / `R1IdealModelV`; the pole term from
`Sem1Uniform`. -/
set_option autoImplicit false
noncomputable section

namespace R1Z.PrivacyR1
open R0P R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort R0Z.HvzkV
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### The composite R1 statement -/

/-- J0c: ZK_FS for the retrying R1 prover (attempts accepted on `P_R1` and no
LogUp pole), with the per-challenge simulator, error
`ε_hit + ε_coll + ε_prog + N · 4096 / Q`. -/
theorem privacy_R1 (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x)
    (ab : AbortBridge K CommitHandle Aux R1Bat fs.Adversary)
    (M Mi q Umin Q : ℕ) (εexh : ℚ) (hU : 0 < Umin) (he : 0 ≤ εexh)
    (hr : R1RealModelV (P_R1 h.transport B hB) h (VR1 h) B outputs fs ab x M q Umin εexh)
    (hi : R1IdealModelV (P_R1 h.transport B hB) h (VR1 h) B outputs fs ab x Mi Umin)
    (hdraw : ∀ adv : fs.Adversary, Sem1Uniform (ab.draw adv x) Q) :
    ZK_FSV h (VR1 h) B outputs fs x
      ((M : ℚ) * q / Umin + ((M : ℚ) * M / Umin + εexh) + (Mi : ℚ) * Mi / Umin +
        ab.N * ((4096 : ℚ) / Q)) :=
  zkfs_of_hvzk_onV_terms (P_R1 h.transport B hB) h (VR1 h) B outputs fs x
    (hvzk_R1V h B hB outputs x hpub hs) ab
    ((M : ℚ) * q / Umin) ((M : ℚ) * M / Umin + εexh) ((Mi : ℚ) * Mi / Umin) ((4096 : ℚ) / Q)
    (by positivity) (add_nonneg (by positivity) he) (by positivity)
    (realAbortCouplingV_of_R1 _ h _ B outputs fs ab x M q Umin εexh hU hr)
    (idealAbortCouplingV_of_R1 _ h _ B outputs fs ab x Mi Umin hU hi)
    (fun adv w _ => (eventMass_mono _ _ (fun c hc => hc.2)).trans
      (pole_mass_le (ab.draw adv x) Q (hdraw adv) (h.build w)))

#print axioms privacy_R1
end R1Z.PrivacyR1
