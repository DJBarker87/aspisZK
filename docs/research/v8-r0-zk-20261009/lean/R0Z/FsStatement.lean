import R0Z.JointView
import R0Z.LawTransport

/-! D11's adopted FS interface. The current 32-round view and a Boolean
observer replace the historical Z1 types. ROMReduction is an explicit open
obligation about the real games, not an instance supplied by this module.
No oracle programming policy, query bound, or numerical error is chosen. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.FsStatement
open R0P R0Z.JointView
attribute [local instance] Classical.propDecidable

abbrev Bytes := List UInt8
abbrev OracleAnswer := Fin 32 → UInt8

/-- Full public model view plus the observer's own query/answer transcript.
The honest prover's private oracle-input log is not a public field. -/
structure ROMView (K CommitHandle Aux Bat : Type) [Field K] where
  disclosed : View K CommitHandle Aux Bat
  observerOracle : List (Bytes × OracleAnswer)

structure FSExperiments (K CommitHandle Aux Bat : Type) [Field K] (F : Subfield K) where
  Adversary : Type
  RealRand : Type
  IdealRand : Type
  real : (h : HonestProver K) → PackBasis F →
    (Statement K CommitHandle → Challenges K → Aux) → Adversary →
    Statement K CommitHandle → h.Instance → RealRand → ROMView K CommitHandle Aux Bat
  ideal : (Challenges K → Tape K F → View K CommitHandle Aux Bat) → Adversary →
    Statement K CommitHandle → IdealRand → ROMView K CommitHandle Aux Bat
  observe : Adversary → ROMView K CommitHandle Aux Bat → Bool

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [HonestView.BatchedLayer K Bat]

def bit (b : Bool) : ℚ := if b then 1 else 0

def realTest (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (w : h.Instance) : fs.RealRand → ℚ :=
  fun r => bit (fs.observe adv (fs.real h B outputs adv x w r))

def idealTest (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (hx : InLanguage h x) : fs.IdealRand → ℚ :=
  fun r => bit (fs.observe adv (fs.ideal (simulator h B outputs x hx) adv x r))

/-- Adopted distinguishing-advantage target. Epsilon remains symbolic;
neither HVZK nor a ROM reduction is a premise of this definition. -/
def ZK_FS (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (epsilon_fs : ℚ) : Prop :=
  ∀ (hx : InLanguage h x) (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
    |mean (realTest h B outputs fs adv x w) - mean (idealTest h B outputs fs adv x hx)| ≤ epsilon_fs

/-- Data for a common randomized extension of the two interactive views.
Its coins include the instance-independent challenge draw and any observer
randomness. Their product with Tape expresses independence from prover coins. -/
structure ROMBridge (K CommitHandle Aux Bat Adv : Type) [Field K] where
  Coins : Type
  finiteCoins : Fintype Coins
  nonemptyCoins : Nonempty Coins
  draw : Adv → Statement K CommitHandle → Coins → Challenges K
  extend : Adv → Statement K CommitHandle → Coins →
    View K CommitHandle Aux Bat → ROMView K CommitHandle Aux Bat

attribute [instance] ROMBridge.finiteCoins ROMBridge.nonemptyCoins

def middleReal (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (bridge : ROMBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (w : h.Instance) : bridge.Coins × Tape K F → ℚ :=
  fun t => bit (fs.observe adv (bridge.extend adv x t.1
    (view h B outputs x w (bridge.draw adv x t.1) t.2)))

def middleIdeal (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (bridge : ROMBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (hx : InLanguage h x) : bridge.Coins × Tape K F → ℚ :=
  fun t => bit (fs.observe adv (bridge.extend adv x t.1
    (simulator h B outputs x hx (bridge.draw adv x t.1) t.2)))

/-- ZF1's substantive obligation: exhibit a common extension and prove both
real-game comparison bounds. All commitment, programming, seed, abort, and
source errors must be justified in these bounds; no such proof is supplied. -/
def ROMReduction (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (epsilon_fs : ℚ) : Prop :=
  ∃ bridge : ROMBridge K CommitHandle Aux Bat fs.Adversary,
    ∃ epsilon_real epsilon_ideal : ℚ,
      0 ≤ epsilon_real ∧ 0 ≤ epsilon_ideal ∧ epsilon_real + epsilon_ideal ≤ epsilon_fs ∧
      ∀ (hx : InLanguage h x) (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
        |mean (realTest h B outputs fs adv x w) -
          mean (middleReal h B outputs fs bridge adv x w)| ≤ epsilon_real ∧
        |mean (middleIdeal h B outputs fs bridge adv x hx) -
          mean (idealTest h B outputs fs adv x hx)| ≤ epsilon_ideal

/-- D20′.3: the two real-game comparison bounds for a specified bridge. -/
def ROMReductionWith (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (bridge : ROMBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (ε_real ε_ideal : ℚ) : Prop :=
  0 ≤ ε_real ∧ 0 ≤ ε_ideal ∧
  ∀ (hx : InLanguage h x) (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
    |mean (realTest h B outputs fs adv x w) -
      mean (middleReal h B outputs fs bridge adv x w)| ≤ ε_real ∧
    |mean (middleIdeal h B outputs fs bridge adv x hx) -
      mean (idealTest h B outputs fs adv x hx)| ≤ ε_ideal

/-- The original reduction existentially packages a bridge and its two bounds. -/
theorem romReduction_iff (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (ε : ℚ) :
    ROMReduction h B outputs fs x ε ↔
      ∃ bridge ε_real ε_ideal,
        ROMReductionWith h B outputs fs bridge x ε_real ε_ideal ∧ ε_real + ε_ideal ≤ ε := by
  constructor
  · rintro ⟨bridge, ε_real, ε_ideal, hr, hi, hsum, hb⟩
    exact ⟨bridge, ε_real, ε_ideal, ⟨hr, hi, hb⟩, hsum⟩
  · rintro ⟨bridge, ε_real, ε_ideal, ⟨hr, hi, hb⟩, hsum⟩
    exact ⟨bridge, ε_real, ε_ideal, hr, hi, hsum, hb⟩

theorem middle_means_eq (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (bridge : ROMBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (hx : InLanguage h x) (w : h.Instance)
    (hw : h.public w = x.1) (hh : HVZK_perfect (Bat := Bat) h B outputs x) :
    mean (middleReal h B outputs fs bridge adv x w) =
      mean (middleIdeal h B outputs fs bridge adv x hx) := by
  rw [LawTransport.mean_product, LawTransport.mean_product]
  apply congrArg mean
  funext coin
  exact LawTransport.mean_eq_of_equalLaws _ _
    (fun v => bit (fs.observe adv (bridge.extend adv x coin v)))
    (hh hx w (bridge.draw adv x coin) hw)

/-- Only the composition is discharged. ZF1 still requires an actual
ROMReduction certificate for the chosen games and their symbolic ledger. -/
theorem zkfs_of_hvzk_perfect (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (epsilon_fs : ℚ) :
    HVZK_perfect (Bat := Bat) h B outputs x → ROMReduction h B outputs fs x epsilon_fs →
      ZK_FS h B outputs fs x epsilon_fs := by
  intro hh hr hx adv w hw
  obtain ⟨bridge, er, ei, _, _, hsum, hb⟩ := hr
  obtain ⟨hr, hi⟩ := hb hx adv w hw
  rw [middle_means_eq h B outputs fs bridge adv x hx w hw hh] at hr
  exact (abs_sub_le _ _ _).trans ((add_le_add hr hi).trans hsum)

#print axioms ZK_FS
#print axioms ROMReduction
#print axioms ROMReductionWith
#print axioms romReduction_iff
#print axioms middle_means_eq
#print axioms zkfs_of_hvzk_perfect
end R0Z.FsStatement
