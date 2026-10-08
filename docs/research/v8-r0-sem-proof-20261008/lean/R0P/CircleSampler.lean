import R0P.SemD2
import R0C.CircleRows
import AspisV8R19.SamplerCirclePolicy

/-!
The lead's total one-block model of the two circle rounds. At Rust inspection
pin e4d68a70d3f6beb215c9f6dd418f4a2a3740c809, the accepted parameter map is
`crates/aspis-core/src/circle.rs:28–65`, used by
`crates/aspis-core/src/transcript.rs:453–465`. `SamplerCirclePolicy.point`
provides the canonical map and its symbolic recovery formula.

The lead's 7d3aa4864 decision counts a rejected block through the prescribed
base-rational sentinel. The source's bounded retry-loop refinement remains
the separate obligation recorded in LOG.md; no byte-uniformity law is used.
-/
set_option autoImplicit false
namespace R0P.SemSource

open AspisWideTower FS
open AspisV8R15.ExactTowerBase AspisV8R15.ExactTowerChord
open AspisV8R19.SamplerCirclePolicy
open AspisR0.Chord AspisR0.ChordGeometry
open R0C.CircleRows R0C.SemStatement R0C.ModuloCounting
open AspisV8R19.SourceDuplexStep
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound

noncomputable section
attribute [local instance] Classical.propDecidable

universe u v

abbrev CircleParam := AspisV5ComponentCQM31TowerExact.QM31Exact

/-- The approved base-rational sentinel for a rejected CM31 parameter. -/
def circleRejectPoint : Point WideExact :=
  baseLift ⟨(1, 0), by norm_num [AspisCircleGroupOrder.OnCircle]⟩

#print axioms circleRejectPoint

/-- The scalar extension of a QM31 circle point into the wide field. -/
def embedCirclePoint (z : Point CircleParam) : Point WideExact :=
  ⟨(algebraMap CircleParam WideExact z.1.1,
      algebraMap CircleParam WideExact z.1.2), by
    have h := congrArg (algebraMap CircleParam WideExact) z.2
    simpa only [AspisCircleGroupOrder.OnCircle, map_add, map_pow, map_one] using h⟩

#print axioms embedCirclePoint

theorem embedCirclePoint_injective : Function.Injective embedCirclePoint := by
  intro z w h
  apply Subtype.ext
  apply Prod.ext
  · exact (algebraMap CircleParam WideExact).injective
      (congrArg (fun q : Point WideExact => q.1.1) h)
  · exact (algebraMap CircleParam WideExact).injective
      (congrArg (fun q : Point WideExact => q.1.2) h)

#print axioms embedCirclePoint_injective

/-- The accepted point map, defined on the source's non-CM31 branch. -/
def circleSampleParameter (t : CircleParam) : Point WideExact :=
  if h : t.im ≠ 0 then
    embedCirclePoint ⟨point t, point_on_circle t (outside_has_denominator t h)⟩
  else circleRejectPoint

#print axioms circleSampleParameter

-- The parameter map's `dite` must never be reduced by the unifier: its
-- decidability instance is the concrete `DecidableEq` of QM31.
attribute [irreducible] circleSampleParameter

/-- One duplex block through the rejection-free QM31 value sampler. -/
def circleSample (s : State) : Point WideExact :=
  circleSampleParameter (qm31Sample s)

#print axioms circleSample

theorem filter_card_eq_of_iff {A : Type u} [Fintype A]
    (P Q : A → Prop) (h : ∀ a, P a ↔ Q a) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  classical
  have hs : Finset.univ.filter P = Finset.univ.filter Q := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h a
  rw [hs]

#print axioms filter_card_eq_of_iff

theorem filter_card_le_rejected_add_one {A B : Type*}
    [Fintype A]
    (bad rejected : A → Prop) (f : A → B) (z : B)
    (hcover : ∀ a, bad a → rejected a ∨ f a = z)
    (hinj : ∀ a b, ¬ rejected a → ¬ rejected b → f a = f b → a = b) :
    (Finset.univ.filter bad).card ≤ (Finset.univ.filter rejected).card + 1 := by
  classical
  let rejectedSet : Finset A := Finset.univ.filter rejected
  let fiber : Finset A := Finset.univ.filter (fun a => ¬ rejected a ∧ f a = z)
  let badSet : Finset A := Finset.univ.filter bad
  have hsub : badSet ⊆ rejectedSet ∪ fiber := by
    intro a ha
    have hb : bad a := by simpa [badSet] using ha
    have hc := hcover a hb
    by_cases hr : rejected a
    · exact Finset.mem_union.mpr (Or.inl (by simp [rejectedSet, hr]))
    · rcases hc with hbad | hfiber
      · exact (hr hbad).elim
      · exact Finset.mem_union.mpr (Or.inr (by simp [fiber, hr, hfiber]))
  have hfiber : fiber.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' : ¬ rejected a ∧ f a = z := by simpa [fiber] using ha
    have hb' : ¬ rejected b ∧ f b = z := by simpa [fiber] using hb
    exact hinj a b ha'.1 hb'.1 (ha'.2.trans hb'.2.symm)
  calc
    (Finset.univ.filter bad).card ≤ (rejectedSet ∪ fiber).card :=
      Finset.card_le_card (by simpa [badSet] using hsub)
    _ ≤ rejectedSet.card + fiber.card := Finset.card_union_le _ _
    _ ≤ (Finset.univ.filter rejected).card + 1 :=
      Nat.add_le_add (by rfl) hfiber

#print axioms filter_card_le_rejected_add_one

theorem cm31_card :
    Fintype.card AspisV5ComponentCQM31TowerExact.CM31Exact =
      AspisV5ComponentCQM31TowerExact.P ^ 2 := by
  have hm31 : Fintype.card AspisV5ComponentCQM31TowerExact.M31Exact =
      AspisV5ComponentCQM31TowerExact.P :=
    ZMod.card AspisV5ComponentCQM31TowerExact.P
  calc
    Fintype.card AspisV5ComponentCQM31TowerExact.CM31Exact =
        Fintype.card (AspisV5ComponentCQM31TowerExact.M31Exact ×
          AspisV5ComponentCQM31TowerExact.M31Exact) :=
      Fintype.card_congr
        (QuadraticAlgebra.equivProd
          (-1 : AspisV5ComponentCQM31TowerExact.M31Exact) 0)
    _ = Fintype.card AspisV5ComponentCQM31TowerExact.M31Exact *
          Fintype.card AspisV5ComponentCQM31TowerExact.M31Exact :=
      Fintype.card_prod _ _
    _ = AspisV5ComponentCQM31TowerExact.P * AspisV5ComponentCQM31TowerExact.P := by
      rw [hm31]
    _ = AspisV5ComponentCQM31TowerExact.P ^ 2 :=
      (pow_two AspisV5ComponentCQM31TowerExact.P).symm

#print axioms cm31_card

def imZeroEquiv :
    {t : CircleParam // t.im = 0} ≃ AspisV5ComponentCQM31TowerExact.CM31Exact where
  toFun t := t.1.re
  invFun z := ⟨algebraMap AspisV5ComponentCQM31TowerExact.CM31Exact CircleParam z, by simp⟩
  left_inv t := by
    apply Subtype.ext
    ext <;> simp [QuadraticAlgebra.algebraMap_eq, t.2]
  right_inv z := by simp

#print axioms imZeroEquiv

theorem imZero_card : Fintype.card {t : CircleParam // t.im = 0} =
    AspisV5ComponentCQM31TowerExact.P ^ 2 := by
  exact (Fintype.card_congr imZeroEquiv).trans cm31_card

#print axioms imZero_card

theorem zmod_algebraMap_comp {p : ℕ} {S : Type u} {R : Type v}
    [CommSemiring S] [Semiring R]
    [Algebra (ZMod p) S] [Algebra S R] [Algebra (ZMod p) R] :
    (algebraMap (ZMod p) R : ZMod p →+* R) =
      (algebraMap S R).comp (algebraMap (ZMod p) S) := by
  exact RingHom.ext_zmod _ _

#print axioms zmod_algebraMap_comp

theorem zmod_algebraMap_pullback {p : ℕ} {S : Type u} {R : Type v}
    [CommSemiring S] [Semiring R]
    [Algebra (ZMod p) S] [Algebra S R] [Algebra (ZMod p) R]
    (hinj : Function.Injective (algebraMap S R))
    (x : ZMod p) (y : S)
    (h : algebraMap (ZMod p) R x = algebraMap S R y) :
    algebraMap (ZMod p) S x = y := by
  apply hinj
  calc
    algebraMap S R (algebraMap (ZMod p) S x) =
        algebraMap (ZMod p) R x := by
      exact (congrArg (fun f : ZMod p →+* R => f x)
        zmod_algebraMap_comp).symm
    _ = algebraMap S R y := h

#print axioms zmod_algebraMap_pullback

/-- The coordinate argument of `CircleSource.parameter_not_rational`,
transported through the injective wide embedding without a scalar-tower premise. -/
theorem embedCirclePoint_not_rational (t : CircleParam) (ht : t.im ≠ 0) :
    ¬ BaseRational (embedCirclePoint ⟨point t,
      point_on_circle t (outside_has_denominator t ht)⟩) := by
  intro hz
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hz
  have hx' : algebraMap (ZMod AspisV5ComponentCQM31TowerExact.P) CircleParam x =
      (point t).1 := by
    exact zmod_algebraMap_pullback
      (p := AspisV5ComponentCQM31TowerExact.P) (S := CircleParam) (R := WideExact)
      (algebraMap CircleParam WideExact).injective x (point t).1 hx
  have hy' : algebraMap (ZMod AspisV5ComponentCQM31TowerExact.P) CircleParam y =
      (point t).2 := by
    exact zmod_algebraMap_pullback
      (p := AspisV5ComponentCQM31TowerExact.P) (S := CircleParam) (R := WideExact)
      (algebraMap CircleParam WideExact).injective y (point t).2 hy
  have hxi : (point t).1.im = 0 := by
    rw [← hx']
    rfl
  have hyi : (point t).2.im = 0 := by
    rw [← hy']
    rfl
  exact outside_point t ht ⟨hxi, hyi⟩

#print axioms embedCirclePoint_not_rational

theorem circleSampleParameter_rational_iff (t : CircleParam) :
    BaseRational (circleSampleParameter t) ↔ t.im = 0 := by
  by_cases ht : t.im = 0
  · simp [circleSampleParameter, ht, circleRejectPoint, baseLift_rational]
  · constructor
    · intro h
      exact ((embedCirclePoint_not_rational t ht) (by
        simpa [circleSampleParameter, ht] using h)).elim
    · intro h
      exact (ht h).elim

#print axioms circleSampleParameter_rational_iff

def circleBadZ0 : Finset CircleParam :=
  Finset.univ.filter (fun t => z0Bad (circleSampleParameter t))

#print axioms circleBadZ0

theorem circleBadZ0_card : circleBadZ0.card =
    AspisV5ComponentCQM31TowerExact.P ^ 2 := by
  rw [circleBadZ0]
  have hcard := filter_card_eq_of_iff
    (fun t : CircleParam => z0Bad (circleSampleParameter t))
    (fun t => t.im = 0) (fun t => circleSampleParameter_rational_iff t)
  rw [hcard]
  exact (Finset.card_eq_of_equiv_fintype
    ((Equiv.subtypeEquivRight (fun t : CircleParam => by simp)).trans imZeroEquiv)).trans cm31_card

#print axioms circleBadZ0_card

section GenericSets
variable {A : Type} [Fintype A]

/-- Every filter predicate here is an atomic variable, so each instantiation
carries the instance `fun a => Classical.propDecidable (p a)` and never a
structured `instDecidableOr`/`instDecidableAnd` term. -/
theorem card_filter_le_add_of_cover (bad p q : A → Prop) (h : ∀ a, bad a → p a ∨ q a) :
    (Finset.univ.filter bad).card ≤ (Finset.univ.filter p).card + (Finset.univ.filter q).card := by
  have hsub : Finset.univ.filter bad ⊆ Finset.univ.filter p ∪ Finset.univ.filter q := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases h a ha.2 with hp | hq
    · exact Or.inl ⟨ha.1, hp⟩
    · exact Or.inr ⟨ha.1, hq⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem card_filter_le_one_of_inj (p : A → Prop) (h : ∀ a b, p a → p b → a = b) :
    (Finset.univ.filter p).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact h a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

end GenericSets

#print axioms card_filter_le_add_of_cover
#print axioms card_filter_le_one_of_inj

/-- Predicates wrapped as definitions: instance search must not build a
concrete `Decidable` instance (the M31/wide `DecidableEq`) for them; a
mismatch with the classical instance makes the unifier evaluate the
decision procedure on the concrete field. -/
def rejectedPred (t : CircleParam) : Prop := t.im = 0
def fiberPred (z0 : Point WideExact) (t : CircleParam) : Prop :=
  t.im ≠ 0 ∧ circleSampleParameter t = z0

theorem z1_cover (z0 : Point WideExact) (t : CircleParam)
    (ht : z1Bad z0 (circleSampleParameter t)) : rejectedPred t ∨ fiberPred z0 t := by
  by_cases hr : t.im = 0
  · exact Or.inl hr
  · rcases ht with h | h
    · exact (hr ((circleSampleParameter_rational_iff t).mp h)).elim
    · exact Or.inr ⟨hr, h⟩

#print axioms z1_cover

theorem z1_inj (t u : CircleParam) (ht : t.im ≠ 0) (hu : u.im ≠ 0)
    (heq : circleSampleParameter t = circleSampleParameter u) : t = u := by
  have hpoints :
      (⟨point t, point_on_circle t (outside_has_denominator t ht)⟩ : Point CircleParam) =
        ⟨point u, point_on_circle u (outside_has_denominator u hu)⟩ := by
    apply embedCirclePoint_injective
    simpa [circleSampleParameter, ht, hu] using heq
  exact point_injective t u (outside_has_denominator t ht) (outside_has_denominator u hu)
    (congrArg Subtype.val hpoints)

#print axioms z1_inj

theorem rejected_card :
    (Finset.univ.filter rejectedPred).card = AspisV5ComponentCQM31TowerExact.P ^ 2 := by
  exact (Finset.card_eq_of_equiv_fintype
    ((Equiv.subtypeEquivRight (fun t : CircleParam => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, rejectedPred])).trans
      imZeroEquiv)).trans cm31_card

#print axioms rejected_card

theorem circleBadZ1_card (z0 : Point WideExact) :
    (Finset.univ.filter
      (fun t : CircleParam => z1Bad z0 (circleSampleParameter t))).card ≤
      AspisV5ComponentCQM31TowerExact.P ^ 2 + 1 := by
  have h1 := card_filter_le_add_of_cover (A := CircleParam)
    (fun t => z1Bad z0 (circleSampleParameter t)) rejectedPred (fiberPred z0) (z1_cover z0)
  have h3 := card_filter_le_one_of_inj (A := CircleParam) (fiberPred z0)
    (fun a b ha hb => z1_inj a b ha.1 hb.1 (ha.2.trans hb.2.symm))
  rw [rejected_card] at h1
  exact h1.trans (Nat.add_le_add_left h3 _)

#print axioms circleBadZ1_card

theorem circle_mass_bound_generic (p n : ℕ) (δ : ℚ)
    (hn : n ≤ p ^ 2 + 1)
    (hp : (3 : ℚ) ≤ (p : ℚ) ^ 2)
    (hδ : δ ≤ (1 : ℚ) / 2) :
    (n : ℚ) * ((1 + δ) / (p : ℚ) ^ 4) ≤ 2 / (p : ℚ) ^ 2 := by
  have hnq : (n : ℚ) ≤ (p : ℚ) ^ 2 + 1 := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℚ) := Nat.cast_nonneg n
  have hdprod : (n : ℚ) * δ ≤ (n : ℚ) / 2 := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hδ hn0
  have hnlin : (n : ℚ) * (1 + δ) ≤ (3 : ℚ) / 2 * n := by
    nlinarith [hdprod]
  have hp2 : (0 : ℚ) < (p : ℚ) ^ 2 := by linarith
  have hscaled :
      (n : ℚ) * (1 + δ) * (p : ℚ) ^ 2 ≤
        (3 : ℚ) / 2 * (n : ℚ) * (p : ℚ) ^ 2 :=
    mul_le_mul_of_nonneg_right hnlin (sq_nonneg (p : ℚ))
  have hnscaled :
      (3 : ℚ) / 2 * (n : ℚ) * (p : ℚ) ^ 2 ≤
        (3 : ℚ) / 2 * ((p : ℚ) ^ 2 + 1) * (p : ℚ) ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnq (by norm_num))
      (sq_nonneg (p : ℚ))
  have hfactor :
      (3 : ℚ) / 2 * ((p : ℚ) ^ 2 + 1) * (p : ℚ) ^ 2 ≤
        2 * ((p : ℚ) ^ 2) ^ 2 := by
    have hq0 : 0 ≤ (p : ℚ) ^ 2 := sq_nonneg _
    have hq3 : 0 ≤ (p : ℚ) ^ 2 - 3 := sub_nonneg.mpr hp
    nlinarith [mul_nonneg hq0 hq3]
  have hprod : (n : ℚ) * (1 + δ) * (p : ℚ) ^ 2 ≤
      2 * (p : ℚ) ^ 4 := by
    calc
      (n : ℚ) * (1 + δ) * (p : ℚ) ^ 2 ≤
          (3 : ℚ) / 2 * (n : ℚ) * (p : ℚ) ^ 2 := hscaled
      _ ≤ (3 : ℚ) / 2 * ((p : ℚ) ^ 2 + 1) * (p : ℚ) ^ 2 := hnscaled
      _ ≤ 2 * ((p : ℚ) ^ 2) ^ 2 := hfactor
      _ = 2 * (p : ℚ) ^ 4 := by ring
  have hp4 : (0 : ℚ) < (p : ℚ) ^ 4 := by
    simpa only [← pow_mul] using pow_pos hp2 2
  rw [show (n : ℚ) * ((1 + δ) / (p : ℚ) ^ 4) =
      ((n : ℚ) * (1 + δ)) / (p : ℚ) ^ 4 by ring]
  rw [div_le_div_iff₀ hp4 hp2]
  exact hprod

#print axioms circle_mass_bound_generic

theorem circle_mass_bound (n : Nat)
    (hn : n ≤ AspisV5ComponentCQM31TowerExact.P ^ 2 + 1) :
    (n : ℚ) * ((1 + deltaQ) /
      (AspisV5ComponentCQM31TowerExact.P : ℚ) ^ 4) ≤
        2 / (AspisV5ComponentCQM31TowerExact.P : ℚ) ^ 2 := by
  apply circle_mass_bound_generic AspisV5ComponentCQM31TowerExact.P n deltaQ hn
  · norm_num [AspisV5ComponentCQM31TowerExact.P]
  · exact deltaQ_small.trans (by norm_num)

#print axioms circle_mass_bound

/-- The first circle row's total one-block sampler mass. -/
theorem circleSample_z0_mass :
    mean (fun s : State => indicator (z0Bad (circleSample s))) ≤
      2 / (AspisV5ComponentCQM31TowerExact.P : ℚ) ^ 2 := by
  let bad := circleBadZ0
  have hmem : ∀ s : State,
      z0Bad (circleSample s) ↔ qm31Sample s ∈ bad := by
    intro s
    change z0Bad (circleSampleParameter (qm31Sample s)) ↔
      qm31Sample s ∈ Finset.univ.filter
        (fun t => z0Bad (circleSampleParameter t))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mean_congr (fun s => indicator_iff (hmem s))]
  calc
    mean (fun s : State => indicator (qm31Sample s ∈ bad)) ≤
        bad.card * ((1 + deltaQ) /
          (AspisV5ComponentCQM31TowerExact.P ^ 4 : ℚ)) :=
      event_mass_le qm31Sample _ qm31Sample_mass_slack bad
    _ ≤ 2 / (AspisV5ComponentCQM31TowerExact.P : ℚ) ^ 2 := by
      apply circle_mass_bound
      have hcard : bad.card = AspisV5ComponentCQM31TowerExact.P ^ 2 := by
        dsimp [bad]
        exact circleBadZ0_card
      rw [hcard]
      exact Nat.le_add_right _ _

#print axioms circleSample_z0_mass

/-- The second circle row's bad mass, including a repeated first point. -/
theorem circleSample_z1_mass (z0 : Point WideExact) :
    mean (fun s : State => indicator (z1Bad z0 (circleSample s))) ≤
      2 / (AspisV5ComponentCQM31TowerExact.P : ℚ) ^ 2 := by
  let bad : Finset CircleParam := Finset.univ.filter
    (fun t => z1Bad z0 (circleSampleParameter t))
  have hmem : ∀ s : State,
      z1Bad z0 (circleSample s) ↔ qm31Sample s ∈ bad := by
    intro s
    change z1Bad z0 (circleSampleParameter (qm31Sample s)) ↔
      qm31Sample s ∈ Finset.univ.filter
        (fun t => z1Bad z0 (circleSampleParameter t))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mean_congr (fun s => indicator_iff (hmem s))]
  calc
    mean (fun s : State => indicator (qm31Sample s ∈ bad)) ≤
        bad.card * ((1 + deltaQ) /
          (AspisV5ComponentCQM31TowerExact.P ^ 4 : ℚ)) :=
      event_mass_le qm31Sample _ qm31Sample_mass_slack bad
    _ ≤ 2 / (AspisV5ComponentCQM31TowerExact.P : ℚ) ^ 2 := by
      apply circle_mass_bound
      exact circleBadZ1_card z0

#print axioms circleSample_z1_mass

end
end R0P.SemSource
