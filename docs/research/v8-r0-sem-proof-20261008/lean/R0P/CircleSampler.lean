import R0P.SemD2
import R0C.CircleRows
import AspisV8R19.SamplerCirclePolicy

/-! G22: total one-block circle samplers with distinct non-rational fallbacks.
Row 24 uses f0 and counts hitting f1; row 25 uses f1 and counts a repetition
of z0. Rejected CM31 parameters introduce no bad mass. Each bad fiber has
at most one parameter, whose mass is bounded by (1+deltaQ)/P^4 under the
existing modulo-reduction sampler. -/
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

def circleFallbackParameter0 : CircleParam := ⟨0, 1⟩
def circleFallbackParameter1 : CircleParam := ⟨1, 1⟩

theorem circleFallbackParameter0_im : circleFallbackParameter0.im ≠ 0 := one_ne_zero
theorem circleFallbackParameter1_im : circleFallbackParameter1.im ≠ 0 := one_ne_zero

theorem circleFallbackParameter_ne : circleFallbackParameter0 ≠ circleFallbackParameter1 := by
  intro h
  exact zero_ne_one (congrArg (fun t : CircleParam => t.re) h)

def circleFallback0 : Point WideExact :=
  embedCirclePoint ⟨point circleFallbackParameter0,
    point_on_circle _ (outside_has_denominator _ circleFallbackParameter0_im)⟩

def circleFallback1 : Point WideExact :=
  embedCirclePoint ⟨point circleFallbackParameter1,
    point_on_circle _ (outside_has_denominator _ circleFallbackParameter1_im)⟩

theorem circleFallback_not_rational :
    ¬ BaseRational circleFallback0 ∧ ¬ BaseRational circleFallback1 :=
  ⟨embedCirclePoint_not_rational _ circleFallbackParameter0_im,
    embedCirclePoint_not_rational _ circleFallbackParameter1_im⟩

/-- Symbolic recovery is applied before specializing the parameter values. -/
theorem embedCirclePoint_parameter_injective (t u : CircleParam)
    (ht : t.im ≠ 0) (hu : u.im ≠ 0)
    (h : embedCirclePoint ⟨point t, point_on_circle t (outside_has_denominator t ht)⟩ =
      embedCirclePoint ⟨point u, point_on_circle u (outside_has_denominator u hu)⟩) : t = u := by
  have he := embedCirclePoint_injective h
  exact point_injective t u (outside_has_denominator t ht) (outside_has_denominator u hu)
    (congrArg (fun z : Point CircleParam => z.val) he)

theorem circleFallback_ne : circleFallback0 ≠ circleFallback1 := by
  intro h
  exact circleFallbackParameter_ne
    (embedCirclePoint_parameter_injective circleFallbackParameter0 circleFallbackParameter1
      circleFallbackParameter0_im circleFallbackParameter1_im h)

#print axioms circleFallbackParameter0_im
#print axioms circleFallbackParameter1_im
#print axioms circleFallbackParameter_ne
#print axioms circleFallback_not_rational
#print axioms circleFallback_ne

/-- Total map with an explicit row-specific fallback; the accepted branch
is unchanged from the source circle parameter map. -/
def circleSampleParameterWith (fallback : Point WideExact) (t : CircleParam) : Point WideExact :=
  if h : t.im ≠ 0 then
    embedCirclePoint ⟨point t, point_on_circle t (outside_has_denominator t h)⟩
  else fallback

attribute [irreducible] circleSampleParameterWith

def circleSampleParameter0 (t : CircleParam) : Point WideExact :=
  circleSampleParameterWith circleFallback0 t

def circleSampleParameter1 (t : CircleParam) : Point WideExact :=
  circleSampleParameterWith circleFallback1 t

def circleSample0 (s : State) : Point WideExact := circleSampleParameter0 (qm31Sample s)
def circleSample1 (s : State) : Point WideExact := circleSampleParameter1 (qm31Sample s)

theorem circleSampleParameterWith_rejected (f : Point WideExact) (t : CircleParam)
    (ht : t.im = 0) : circleSampleParameterWith f t = f := by
  simp only [circleSampleParameterWith, ht, ne_eq, not_true_eq_false, ↓reduceDIte]

theorem circleSampleParameterWith_accepted (f : Point WideExact) (t : CircleParam)
    (ht : t.im ≠ 0) : circleSampleParameterWith f t =
      embedCirclePoint ⟨point t, point_on_circle t (outside_has_denominator t ht)⟩ := by
  simp only [circleSampleParameterWith, dif_pos ht]

theorem circleSampleParameterWith_not_rational (f : Point WideExact) (hf : ¬ BaseRational f)
    (t : CircleParam) : ¬ BaseRational (circleSampleParameterWith f t) := by
  by_cases ht : t.im = 0
  · rw [circleSampleParameterWith_rejected f t ht]
    exact hf
  · rw [circleSampleParameterWith_accepted f t ht]
    exact embedCirclePoint_not_rational t ht

theorem circleSampleParameter0_not_rational (t : CircleParam) :
    ¬ BaseRational (circleSampleParameter0 t) :=
  circleSampleParameterWith_not_rational _ circleFallback_not_rational.1 t

theorem circleSampleParameter1_not_rational (t : CircleParam) :
    ¬ BaseRational (circleSampleParameter1 t) :=
  circleSampleParameterWith_not_rational _ circleFallback_not_rational.2 t

theorem circleSampleParameterWith_inj (f : Point WideExact) (t u : CircleParam)
    (ht : t.im ≠ 0) (hu : u.im ≠ 0)
    (h : circleSampleParameterWith f t = circleSampleParameterWith f u) : t = u := by
  rw [circleSampleParameterWith_accepted f t ht, circleSampleParameterWith_accepted f u hu] at h
  exact embedCirclePoint_parameter_injective t u ht hu h

/-- The source first-row event at the fixed second-row fallback. -/
def z0Bad' (z : Point WideExact) : Prop := z0Bad circleFallback1 z

/-- Atomic predicates for all concrete filter and cardinality expressions. -/
def circleBad0Pred (t : CircleParam) : Prop := z0Bad' (circleSampleParameter0 t)
def circleBad1Pred (z0 : Point WideExact) (t : CircleParam) : Prop :=
  z1Bad z0 (circleSampleParameter1 t)

theorem circleBad0_fiber (t : CircleParam) (h : circleBad0Pred t) :
    t.im ≠ 0 ∧ circleSampleParameter0 t = circleFallback1 := by
  rcases h with hr | he
  · exact (circleSampleParameter0_not_rational t hr).elim
  · refine ⟨?_, he⟩
    intro ht
    change circleSampleParameterWith circleFallback0 t = circleFallback1 at he
    rw [circleSampleParameterWith_rejected _ t ht] at he
    exact circleFallback_ne he

theorem circleBad1_fiber (z0 : Point WideExact) (hz0 : z0 ≠ circleFallback1)
    (t : CircleParam) (h : circleBad1Pred z0 t) :
    t.im ≠ 0 ∧ circleSampleParameter1 t = z0 := by
  rcases h with hr | he
  · exact (circleSampleParameter1_not_rational t hr).elim
  · refine ⟨?_, he⟩
    intro ht
    change circleSampleParameterWith circleFallback1 t = z0 at he
    rw [circleSampleParameterWith_rejected _ t ht] at he
    exact hz0 he.symm

theorem circleBad0_card : (Finset.univ.filter circleBad0Pred).card ≤ 1 := by
  apply card_filter_le_one_of_inj circleBad0Pred
  intro t u ht hu
  obtain ⟨ht, he⟩ := circleBad0_fiber t ht
  obtain ⟨hu, he'⟩ := circleBad0_fiber u hu
  exact circleSampleParameterWith_inj circleFallback0 t u ht hu (he.trans he'.symm)

theorem circleBad1_card (z0 : Point WideExact) (hz0 : z0 ≠ circleFallback1) :
    (Finset.univ.filter (circleBad1Pred z0)).card ≤ 1 := by
  apply card_filter_le_one_of_inj (circleBad1Pred z0)
  intro t u ht hu
  obtain ⟨ht, he⟩ := circleBad1_fiber z0 hz0 t ht
  obtain ⟨hu, he'⟩ := circleBad1_fiber z0 hz0 u hu
  exact circleSampleParameterWith_inj circleFallback1 t u ht hu (he.trans he'.symm)

theorem circleSampleParameter0_f1 :
    circleSampleParameter0 circleFallbackParameter1 = circleFallback1 := by
  exact circleSampleParameterWith_accepted _ _ circleFallbackParameter1_im

theorem circleBad0_iff (t : CircleParam) : circleBad0Pred t ↔ t = circleFallbackParameter1 := by
  constructor
  · intro ht
    obtain ⟨ht, he⟩ := circleBad0_fiber t ht
    exact circleSampleParameterWith_inj circleFallback0 t circleFallbackParameter1
      ht circleFallbackParameter1_im (he.trans circleSampleParameter0_f1.symm)
  · rintro rfl
    exact Or.inr circleSampleParameter0_f1

theorem circleSample0_bad_iff (s : State) :
    z0Bad' (circleSample0 s) ↔ qm31Sample s = circleFallbackParameter1 :=
  circleBad0_iff (qm31Sample s)

#print axioms circleSampleParameter0_not_rational
#print axioms circleSampleParameter1_not_rational
#print axioms circleBad0_card
#print axioms circleBad1_card
#print axioms circleSample0_bad_iff


/-- The two imported prime constants denote the same rational number. -/
theorem circlePrime_eq : (AspisV5ComponentCQM31TowerExact.P : ℚ) =
    AspisCircleGroupOrder.P := by
  norm_num [AspisV5ComponentCQM31TowerExact.P, AspisCircleGroupOrder.P]

#print axioms circlePrime_eq

/-- The first row's single bad parameter, including the modulo slack. -/
theorem circleSample0_mass :
    mean (fun s : State => indicator (z0Bad' (circleSample0 s))) ≤
      (1 + deltaQ) / (AspisV5ComponentCQM31TowerExact.P : ℚ)^4 := by
  let bad : Finset CircleParam := Finset.univ.filter circleBad0Pred
  have hmem : ∀ s : State, z0Bad' (circleSample0 s) ↔ qm31Sample s ∈ bad := by
    intro s
    change circleBad0Pred (qm31Sample s) ↔ qm31Sample s ∈ Finset.univ.filter circleBad0Pred
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mean_congr (fun s => indicator_iff (hmem s))]
  have hm := event_mass_le qm31Sample _ qm31Sample_mass_slack bad
  rw [← circlePrime_eq] at hm
  have hc : (bad.card : ℚ) ≤ 1 := by exact_mod_cast circleBad0_card
  have hn : 0 ≤ (1 + deltaQ) / (AspisV5ComponentCQM31TowerExact.P : ℚ)^4 :=
    div_nonneg (add_nonneg zero_le_one deltaQ_nonneg) (pow_nonneg (Nat.cast_nonneg _) _)
  exact hm.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hn)

/-- The second row's fiber bound; the preceding non-bad row excludes f1. -/
theorem circleSample1_mass (z0 : Point WideExact) (hz0 : z0 ≠ circleFallback1) :
    mean (fun s : State => indicator (z1Bad z0 (circleSample1 s))) ≤
      (1 + deltaQ) / (AspisV5ComponentCQM31TowerExact.P : ℚ)^4 := by
  let bad : Finset CircleParam := Finset.univ.filter (circleBad1Pred z0)
  have hmem : ∀ s : State, z1Bad z0 (circleSample1 s) ↔ qm31Sample s ∈ bad := by
    intro s
    change circleBad1Pred z0 (qm31Sample s) ↔ qm31Sample s ∈ Finset.univ.filter (circleBad1Pred z0)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mean_congr (fun s => indicator_iff (hmem s))]
  have hm := event_mass_le qm31Sample _ qm31Sample_mass_slack bad
  rw [← circlePrime_eq] at hm
  have hc : (bad.card : ℚ) ≤ 1 := by exact_mod_cast circleBad1_card z0 hz0
  have hn : 0 ≤ (1 + deltaQ) / (AspisV5ComponentCQM31TowerExact.P : ℚ)^4 :=
    div_nonneg (add_nonneg zero_le_one deltaQ_nonneg) (pow_nonneg (Nat.cast_nonneg _) _)
  exact hm.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hn)

#print axioms circleSample0_mass
#print axioms circleSample1_mass
end
end R0P.SemSource
