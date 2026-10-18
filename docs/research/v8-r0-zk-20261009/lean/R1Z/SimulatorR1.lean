import R1Z.RefCosetR1
import R1Z.MaskImageVR1
import R1Z.PoleMassR1
import R1Z.ModelsVR1
import R0Z.HvzkS

/-! ZF2 (zf1/DESIGN-ZF2-SIMULATOR.txt §5.3): the R1 privacy theorem with the
explicit simulator `simE` in place of the choice simulator `simV`.

* `hvzk_R1S`: on `P_R1` and the pole-free valid set `VR1`, every honest view
  has the law of `simE h.transport B outputs x ch` (clause (i′), Claim Z,
  `equalLaws_simE_of`).
* `R1IdealModelS`: `R1IdealModelV` with the agreement field naming the games
  of the given simulator; `idealAbortCouplingS_of_R1` as in ModelsVR1.
* `privacy_R1_eff`: ZK_FS against `simE`, with the error terms of
  `privacy_R1`. -/
set_option autoImplicit false
noncomputable section

namespace R1Z.SimulatorR1
open R0P R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS
  R0Z.RefPayload R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1
  R1Z.RefCosetR1
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- HVZK on `P_R1` and the pole-free valid set against the explicit simulator. -/
theorem hvzk_R1S (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x) :
    HVZK_onS (Bat := R1Bat) (P_R1 h.transport B hB) h (VR1 h) B outputs x
      (simE h.transport B outputs x) := by
  intro w ch hP hV hw
  have hF := R0Z.HonestValidity.baseTyped_of h B x hs
  have hval : R0Z.HonestValid.HonestValid x.1 B (h.build w) ch :=
    R0Z.HonestValidity.honestValid_of x.1 B (h.build w) ch (hs w hw) hV
  exact equalLaws_simE_of h B outputs x w ch
    (fun n => R1Z.ClauseIR1.clause_i_R1_all h B hB x hpub hF ch hP w n hw)
    (cTilde_sub_ref_mem_range_R1 h B hB x hpub ch hP w (hF w hw) hval)

/-- `R1IdealModelV` (LOG D41, D42.2) for a given simulator. -/
def R1IdealModelS (P : Challenges K → Prop)
    (fs : FSExperiments K CommitHandle Aux R1Bat F) [Fintype fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux R1Bat fs.Adversary)
    (x : Statement K CommitHandle) (M Umin : ℕ)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat) : Prop :=
  ∀ (adv : fs.Adversary),
    ∃ (cp : Coupling fs.IdealRand ((Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F)))
      (priv : Fin M → Prop) (addr : Fin M → cp.S → Bytes),
      (∀ s, ¬ R0Z.FsAbortBounds.CollEv M priv addr s →
        middleIdealAbortS P fs ab adv x sim (cp.toM s) = idealTestS fs adv x sim (cp.toR s)) ∧
      (∀ j j', j < j' → (priv j ∨ priv j') →
        R0Z.FsAbortBounds.PairFresh (addr j) (addr j') Umin ∨
          R0Z.FsAbortBounds.PairFresh (addr j') (addr j) Umin)

theorem idealAbortCouplingS_of_R1 (P : Challenges K → Prop)
    (fs : FSExperiments K CommitHandle Aux R1Bat F) [Fintype fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux R1Bat fs.Adversary)
    (x : Statement K CommitHandle) (M Umin : ℕ) (hU : 0 < Umin)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat)
    (hm : R1IdealModelS P fs ab x M Umin sim) :
    IdealAbortCouplingS P fs ab x sim ((M : ℚ) * M / Umin) := by
  intro adv
  obtain ⟨cp, priv, addr, hag, hpair⟩ := hm adv
  refine ⟨cp, R0Z.FsAbortBounds.CollEv M priv addr, hag, ?_⟩
  rw [R0Z.FsAbortR1.eventMass_eq_mass]
  exact R0Z.FsAbortBounds.collEv_mass_fresh M Umin hU priv addr hpair

/-- ZF2: ZK_FS for the retrying R1 prover against the explicit simulator
`simE`, error `ε_hit + ε_coll + ε_prog + N · 4096 / Q` (as `privacy_R1`). -/
theorem privacy_R1_eff (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x)
    (ab : AbortBridge K CommitHandle Aux R1Bat fs.Adversary)
    (M Mi q Umin Q : ℕ) (εexh : ℚ) (hU : 0 < Umin)
    (hr : R1RealModelV (P_R1 h.transport B hB) h (VR1 h) B outputs fs ab x M q Umin εexh)
    (hi : R1IdealModelS (P_R1 h.transport B hB) fs ab x Mi Umin (simE h.transport B outputs x))
    (hdraw : ∀ adv : fs.Adversary, Sem1Uniform (ab.draw adv x) Q) :
    ZK_FSS h B outputs fs x (simE h.transport B outputs x)
      ((M : ℚ) * q / Umin + ((M : ℚ) * M / Umin + εexh) + (Mi : ℚ) * Mi / Umin +
        ab.N * ((4096 : ℚ) / Q)) :=
  zkfs_of_hvzk_onS_terms (P_R1 h.transport B hB) h (VR1 h) B outputs fs x
    (simE h.transport B outputs x) (hvzk_R1S h B hB outputs x hpub hs) ab
    ((M : ℚ) * q / Umin) ((M : ℚ) * M / Umin + εexh) ((Mi : ℚ) * Mi / Umin) ((4096 : ℚ) / Q)
    (realAbortCouplingV_of_R1 _ h _ B outputs fs ab x M q Umin εexh hU hr)
    (idealAbortCouplingS_of_R1 _ fs ab x Mi Umin hU _ hi)
    (fun adv w _ => (eventMass_mono _ _ (fun c hc => hc.2)).trans
      (pole_mass_le (ab.draw adv x) Q (hdraw adv) (h.build w)))

#print axioms hvzk_R1S
#print axioms R1IdealModelS
#print axioms idealAbortCouplingS_of_R1
#print axioms privacy_R1_eff
end R1Z.SimulatorR1
