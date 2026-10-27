import R0Z.HvzkV
import R0Z.FsAbortR1
import R1Z.Batched

/-! J0c (LOG D41): the ZF1 R1 models for the pole-aware retry games.  The
fields are those of `R0Z.FsAbortR1.R1RealModel` / `R1IdealModel`; only the
agreement field names `middleRealAbortV` (attempts accepted on `P ∧ V`) and
the per-challenge simulator games.  The coupling bounds are proved from
`FsAbortBounds` exactly as in `FsAbortR1`. -/
set_option autoImplicit false
noncomputable section

namespace R1Z.ModelsVR1
open R0P R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort R0Z.HvzkV
  R1Z.Batched
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### The ZF1 R1 models for the pole-aware games -/

/-- `R1RealModel` (LOG D41) with the agreement field naming `middleRealAbortV`. -/
def R1RealModelV (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux R1Bat F) [Fintype fs.RealRand]
    (ab : AbortBridge K CommitHandle Aux R1Bat fs.Adversary)
    (x : Statement K CommitHandle) (M q Umin : ℕ) (εexh : ℚ) : Prop :=
  ∀ (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
    ∃ (cp : Coupling fs.RealRand ((Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F)))
      (charged : Fin M → cp.S → Prop) (priv : Fin M → Prop)
      (addr : Fin M → cp.S → Bytes) (qry : Fin q → cp.S → Bytes) (exh : cp.S → Prop),
      (∀ s, ¬ R0Z.FsAbortBounds.HitEv M q charged qry addr s →
          ¬ (R0Z.FsAbortBounds.CollEv M priv addr s ∨ exh s) →
        realTest h B outputs fs adv x w (cp.toR s) =
          middleRealAbortV P h V B outputs fs ab adv x w (cp.toM s)) ∧
      (∀ j i, R0Z.FsAbortBounds.HitFresh (charged j) (qry i) (addr j) Umin) ∧
      (∀ j j', j < j' → (priv j ∨ priv j') →
        R0Z.FsAbortBounds.PairFresh (addr j) (addr j') Umin ∨
          R0Z.FsAbortBounds.PairFresh (addr j') (addr j) Umin) ∧
      R0Z.FsAbortBounds.mass exh ≤ εexh

/-- `R1IdealModel` (LOG D41) with the agreement field naming the per-challenge
simulator games. -/
def R1IdealModelV (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux R1Bat F) [Fintype fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux R1Bat fs.Adversary)
    (x : Statement K CommitHandle) (M Umin : ℕ) : Prop :=
  ∀ (hx : InLanguage h x) (adv : fs.Adversary),
    ∃ (cp : Coupling fs.IdealRand ((Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F)))
      (priv : Fin M → Prop) (addr : Fin M → cp.S → Bytes),
      (∀ s, ¬ R0Z.FsAbortBounds.CollEv M priv addr s →
        middleIdealAbortV P h V B outputs fs ab adv x hx (cp.toM s) =
          idealTestV h V B outputs fs adv x hx (cp.toR s)) ∧
      (∀ j j', j < j' → (priv j ∨ priv j') →
        R0Z.FsAbortBounds.PairFresh (addr j) (addr j') Umin ∨
          R0Z.FsAbortBounds.PairFresh (addr j') (addr j) Umin)

theorem realAbortCouplingV_of_R1 (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux R1Bat F) [Fintype fs.RealRand]
    (ab : AbortBridge K CommitHandle Aux R1Bat fs.Adversary)
    (x : Statement K CommitHandle) (M q Umin : ℕ) (εexh : ℚ) (hU : 0 < Umin)
    (hm : R1RealModelV P h V B outputs fs ab x M q Umin εexh) :
    RealAbortCouplingV P h V B outputs fs ab x ((M : ℚ) * q / Umin)
      ((M : ℚ) * M / Umin + εexh) := by
  intro adv w hw
  obtain ⟨cp, charged, priv, addr, qry, exh, hag, hhit, hpair, hexh⟩ := hm adv w hw
  refine ⟨cp, R0Z.FsAbortBounds.HitEv M q charged qry addr,
    fun s => R0Z.FsAbortBounds.CollEv M priv addr s ∨ exh s, hag, ?_, ?_⟩
  · rw [R0Z.FsAbortR1.eventMass_eq_mass]
    exact R0Z.FsAbortBounds.hitEv_mass_fresh M q Umin hU charged qry addr hhit
  · rw [R0Z.FsAbortR1.eventMass_eq_mass]
    calc R0Z.FsAbortBounds.mass (fun s => R0Z.FsAbortBounds.CollEv M priv addr s ∨ exh s)
        ≤ R0Z.FsAbortBounds.mass (R0Z.FsAbortBounds.CollEv M priv addr) +
            R0Z.FsAbortBounds.mass exh :=
          R0Z.FsAbortBounds.mass_or_le _ _
      _ ≤ (M : ℚ) * M / Umin + εexh :=
          add_le_add (R0Z.FsAbortBounds.collEv_mass_fresh M Umin hU priv addr hpair) hexh

theorem idealAbortCouplingV_of_R1 (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux R1Bat F) [Fintype fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux R1Bat fs.Adversary)
    (x : Statement K CommitHandle) (M Umin : ℕ) (hU : 0 < Umin)
    (hm : R1IdealModelV P h V B outputs fs ab x M Umin) :
    IdealAbortCouplingV P h V B outputs fs ab x ((M : ℚ) * M / Umin) := by
  intro hx adv
  obtain ⟨cp, priv, addr, hag, hpair⟩ := hm hx adv
  refine ⟨cp, R0Z.FsAbortBounds.CollEv M priv addr, hag, ?_⟩
  rw [R0Z.FsAbortR1.eventMass_eq_mass]
  exact R0Z.FsAbortBounds.collEv_mass_fresh M Umin hU priv addr hpair

#print axioms R1RealModelV
#print axioms R1IdealModelV
#print axioms realAbortCouplingV_of_R1
#print axioms idealAbortCouplingV_of_R1
end R1Z.ModelsVR1
