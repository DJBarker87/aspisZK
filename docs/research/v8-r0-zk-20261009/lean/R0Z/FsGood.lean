import R0Z.FsStatement
import R0Z.Shift

/-! D17.2 item 9: the FS ledger term of statistical HVZK. The middle
experiments agree exactly on the coins whose drawn challenge satisfies `P`,
and differ by at most one on the rest because the observer bit is 0/1-valued.
`badMass P` is that remaining mass; identifying it with `21/|K_α|` is ZF1's
obligation and needs the FS draw's alpha-row law, which is not chosen here. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.FsGood
open R0P R0Z.JointView R0Z.FsStatement R0Z.Shift
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [HonestView.BatchedLayer K Bat]

/-! ### Elementary facts about finite uniform means -/

theorem mean_sub {R : Type} [Fintype R] (f g : R → ℚ) :
    mean f - mean g = mean (fun r => f r - g r) := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

theorem abs_mean_le {R : Type} [Fintype R] (f : R → ℚ) :
    |mean f| ≤ mean (fun r => |f r|) := by
  unfold mean
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℚ) (Fintype.card R))]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

theorem mean_le_mean {R : Type} [Fintype R] (f g : R → ℚ) (h : ∀ r, f r ≤ g r) :
    mean f ≤ mean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun r _ => h r)) (Nat.cast_nonneg _)

theorem mean_nonneg {R : Type} [Fintype R] (f : R → ℚ) (h : ∀ r, 0 ≤ f r) : 0 ≤ mean f :=
  div_nonneg (Finset.sum_nonneg (fun r _ => h r)) (Nat.cast_nonneg _)

theorem mean_le_one {R : Type} [Fintype R] (f : R → ℚ) (h : ∀ r, f r ≤ 1) : mean f ≤ 1 := by
  unfold mean
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  have hs := Finset.sum_le_card_nsmul Finset.univ f 1 (fun r _ => h r)
  simpa only [Finset.card_univ, nsmul_eq_mul, mul_one] using hs

theorem bit_nonneg (b : Bool) : 0 ≤ bit b := by
  unfold bit
  split_ifs <;> norm_num

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by
  unfold bit
  split_ifs <;> norm_num

/-! ### The ledger term -/

/-- The mass of bridge coins whose drawn challenge fails `P`. -/
def badMass {Adv : Type} (P : Challenges K → Prop) (bridge : ROMBridge K CommitHandle Aux Bat Adv)
    (adv : Adv) (x : Statement K CommitHandle) : ℚ :=
  mean (fun coin => if P (bridge.draw adv x coin) then 0 else 1)

/-- `middle_means_eq` on the good coins; a difference of at most one elsewhere. -/
theorem middle_means_close (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (bridge : ROMBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (hx : InLanguage h x) (w : h.Instance)
    (hw : h.public w = x.1) (P : Challenges K → Prop) (hh : HVZK_on (Bat := Bat) P h B outputs x) :
    |mean (middleReal h B outputs fs bridge adv x w) -
      mean (middleIdeal h B outputs fs bridge adv x hx)| ≤ badMass P bridge adv x := by
  rw [LawTransport.mean_product, LawTransport.mean_product, mean_sub]
  refine (abs_mean_le _).trans (mean_le_mean _ _ ?_)
  intro coin
  by_cases hP : P (bridge.draw adv x coin)
  · rw [if_pos hP]
    have heq : mean (fun r => middleReal h B outputs fs bridge adv x w (coin, r)) =
        mean (fun r => middleIdeal h B outputs fs bridge adv x hx (coin, r)) :=
      LawTransport.mean_eq_of_equalLaws _ _
        (fun v => bit (fs.observe adv (bridge.extend adv x coin v)))
        (hh hx w (bridge.draw adv x coin) hP hw)
    simp only [heq, sub_self, abs_zero, le_refl]
  · rw [if_neg hP]
    have h1 : 0 ≤ mean (fun r => middleReal h B outputs fs bridge adv x w (coin, r)) :=
      mean_nonneg _ (fun r => bit_nonneg _)
    have h2 : mean (fun r => middleReal h B outputs fs bridge adv x w (coin, r)) ≤ 1 :=
      mean_le_one _ (fun r => bit_le_one _)
    have h3 : 0 ≤ mean (fun r => middleIdeal h B outputs fs bridge adv x hx (coin, r)) :=
      mean_nonneg _ (fun r => bit_nonneg _)
    have h4 : mean (fun r => middleIdeal h B outputs fs bridge adv x hx (coin, r)) ≤ 1 :=
      mean_le_one _ (fun r => bit_le_one _)
    rw [abs_sub_le_iff]
    constructor <;> linarith

/-- D20′.3: statistical HVZK on `P` composed using the specified bridge's bad mass. -/
theorem zkfs_of_hvzk_on_bridge (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (P : Challenges K → Prop) (hh : HVZK_on (Bat := Bat) P h B outputs x)
    (bridge : ROMBridge K CommitHandle Aux Bat fs.Adversary) (ε_real ε_ideal ε_bad : ℚ)
    (hr : ROMReductionWith h B outputs fs bridge x ε_real ε_ideal)
    (hmass : ∀ adv, badMass P bridge adv x ≤ ε_bad) :
    ZK_FS h B outputs fs x (ε_real + ε_ideal + ε_bad) := by
  intro hx adv w hw
  obtain ⟨_, _, hb⟩ := hr
  obtain ⟨hreal, hideal⟩ := hb hx adv w hw
  have hmid := middle_means_close h B outputs fs bridge adv x hx w hw P hh
  have hbad := hmass adv
  have t1 := abs_sub_le (mean (realTest h B outputs fs adv x w))
    (mean (middleReal h B outputs fs bridge adv x w)) (mean (idealTest h B outputs fs adv x hx))
  have t2 := abs_sub_le (mean (middleReal h B outputs fs bridge adv x w))
    (mean (middleIdeal h B outputs fs bridge adv x hx)) (mean (idealTest h B outputs fs adv x hx))
  linarith

/-- D20′.3: mask image on `Good` composed with the specified bridge's reduction and bad mass. -/
theorem zkfs_of_maskImageOn_good_bridge [Fintype Bat] (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle)
    (bridge : ROMBridge K CommitHandle Aux Bat fs.Adversary) (ε_real ε_ideal ε_bad : ℚ) :
    MaskImageOn (Bat := Bat) Good h B x → ROMReductionWith h B outputs fs bridge x ε_real ε_ideal →
    (∀ adv, badMass Good bridge adv x ≤ ε_bad) →
    ZK_FS h B outputs fs x (ε_real + ε_ideal + ε_bad) :=
  fun hm hr hmass => zkfs_of_hvzk_on_bridge h B outputs fs x Good
    (hvzk_on_good h B outputs x hm) bridge ε_real ε_ideal ε_bad hr hmass

/-- D17.2 item 9: statistical HVZK on `P` composed with a ROM reduction;
superseded by the `_bridge` forms (D20′.3). -/
theorem zkfs_of_hvzk_on (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (P : Challenges K → Prop) (epsilon_fs epsilon_bad : ℚ)
    (hh : HVZK_on (Bat := Bat) P h B outputs x) (hr : ROMReduction h B outputs fs x epsilon_fs)
    (hmass : ∀ (bridge : ROMBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary),
      badMass P bridge adv x ≤ epsilon_bad) :
    ZK_FS h B outputs fs x (epsilon_fs + epsilon_bad) := by
  intro hx adv w hw
  obtain ⟨bridge, er, ei, _, _, hsum, hb⟩ := hr
  obtain ⟨hreal, hideal⟩ := hb hx adv w hw
  have hmid := middle_means_close h B outputs fs bridge adv x hx w hw P hh
  have hbad := hmass bridge adv
  have t1 := abs_sub_le (mean (realTest h B outputs fs adv x w))
    (mean (middleReal h B outputs fs bridge adv x w)) (mean (idealTest h B outputs fs adv x hx))
  have t2 := abs_sub_le (mean (middleReal h B outputs fs bridge adv x w))
    (mean (middleIdeal h B outputs fs bridge adv x hx)) (mean (idealTest h B outputs fs adv x hx))
  linarith

/-- The Lean form of "statistical HVZK with the 21/|K_α| term": perfect on `Good`
plus one named ledger term; superseded by the `_bridge` forms (D20′.3). -/
theorem zkfs_of_maskImageOn_good [Fintype Bat] (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (epsilon_fs epsilon_bad : ℚ) :
    MaskImageOn (Bat := Bat) Good h B x → ROMReduction h B outputs fs x epsilon_fs →
    (∀ (bridge : ROMBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary),
      badMass Good bridge adv x ≤ epsilon_bad) →
    ZK_FS h B outputs fs x (epsilon_fs + epsilon_bad) :=
  fun hm hr hmass => zkfs_of_hvzk_on h B outputs fs x Good epsilon_fs epsilon_bad
    (hvzk_on_good h B outputs x hm) hr hmass

#print badMass
#print axioms middle_means_close
#print axioms zkfs_of_hvzk_on_bridge
#print axioms zkfs_of_maskImageOn_good_bridge
#print axioms zkfs_of_hvzk_on
#print axioms zkfs_of_maskImageOn_good
end R0Z.FsGood
