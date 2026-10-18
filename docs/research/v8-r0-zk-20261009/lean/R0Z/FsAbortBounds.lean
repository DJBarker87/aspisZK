import R0Z.LawTransport

/-! ZF1a/b (DESIGN-ZF1-COUPLINGS-R1 §5, §7): generic event-mass bounds for the
abort couplings. Everything here is over an arbitrary finite uniform space
`S`; nothing refers to the payload, the transcript or a concrete oracle.

* `mass` is the uniform mass of an event (the body of `FsAbort.eventMass`).
* union bounds over finite index sets (`mass_exists_le_card`);
* the conditioning step (`mass_cond_le`): if `S ≃ R × X`, an event `D` depends
  on `R` only and, for every `r` with `D`, the `X`-mass of `E` is at most `δ`,
  then `mass (D ∧ E) ≤ mass D * δ`;
* the first-read step (`hit_le`, `hitFresh_mass`): a read whose address does
  not move when a coordinate `u` moves, compared with an address that
  determines `u` (a designated field), agrees with probability `≤ 1/|U|`;
* the pair step (`pair_le`, `pairFresh_mass`) for prover-address collisions;
* the assembled events `HitEv` (charged reads hit by the adversary) and
  `CollEv` (address repetition among positions, at least one private), with
  `hitEv_mass_le : ≤ M*q/Umin` and `collEv_mass_le : ≤ M*M/Umin`.

The concrete facts (which coordinate is the designated field of which read,
and that the adversary's reads do not depend on it) are the hypotheses
`HitFresh` / `PairFresh`; they are source-correspondence facts about the R1
byte layout, not proved here. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.FsAbortBounds
attribute [local instance] Classical.propDecidable

/-! ### Uniform means -/

theorem mean_equiv' {R S : Type} [Fintype R] [Fintype S] (e : R ≃ S) (f : R → ℚ) :
    mean f = mean (fun s => f (e.symm s)) := by
  unfold mean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e f (fun s => f (e.symm s)) (fun r => by simp)

theorem mean_mono' {R : Type} [Fintype R] (f g : R → ℚ) (h : ∀ r, f r ≤ g r) :
    mean f ≤ mean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun r _ => h r)) (Nat.cast_nonneg _)

theorem mean_sum' {R ι : Type} [Fintype R] [Fintype ι] (f : ι → R → ℚ) :
    mean (fun r => ∑ i, f i r) = ∑ i, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem mean_add'' {R : Type} [Fintype R] (f g : R → ℚ) :
    mean (fun r => f r + g r) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_mul_const {R : Type} [Fintype R] (f : R → ℚ) (c : ℚ) :
    mean (fun r => f r * c) = mean f * c := by
  unfold mean
  rw [← Finset.sum_mul]
  ring

theorem mean_const' {R : Type} [Fintype R] [Nonempty R] (c : ℚ) :
    mean (fun _ : R => c) = c := by
  unfold mean
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h : (Fintype.card R : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-! ### Event mass -/

/-- Uniform mass of an event; the same body as `FsAbort.eventMass`. -/
def mass {S : Type} [Fintype S] (E : S → Prop) : ℚ :=
  mean (fun s => if E s then (1 : ℚ) else 0)

theorem ind_nonneg (p : Prop) : 0 ≤ (if p then (1 : ℚ) else 0) := by
  split_ifs <;> norm_num

theorem ind_le_one (p : Prop) : (if p then (1 : ℚ) else 0) ≤ 1 := by
  split_ifs <;> norm_num

theorem mass_nonneg {S : Type} [Fintype S] (E : S → Prop) : 0 ≤ mass E :=
  div_nonneg (Finset.sum_nonneg (fun s _ => ind_nonneg (E s))) (Nat.cast_nonneg _)

theorem mass_le_one {S : Type} [Fintype S] (E : S → Prop) : mass E ≤ 1 := by
  unfold mass mean
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  have hs := Finset.sum_le_card_nsmul Finset.univ (fun s => if E s then (1 : ℚ) else 0) 1
    (fun s _ => ind_le_one (E s))
  simpa only [Finset.card_univ, nsmul_eq_mul, mul_one] using hs

theorem mass_mono {S : Type} [Fintype S] (E E' : S → Prop) (h : ∀ s, E s → E' s) :
    mass E ≤ mass E' := by
  apply mean_mono'
  intro s
  by_cases h1 : E s
  · rw [if_pos h1, if_pos (h s h1)]
  · rw [if_neg h1]
    exact ind_nonneg (E' s)

theorem mass_congr {S : Type} [Fintype S] (E E' : S → Prop) (h : ∀ s, E s ↔ E' s) :
    mass E = mass E' :=
  le_antisymm (mass_mono E E' (fun s => (h s).mp)) (mass_mono E' E (fun s => (h s).mpr))

theorem mass_false {S : Type} [Fintype S] : mass (fun _ : S => False) = 0 := by
  simp [mass, mean]

theorem mass_true {S : Type} [Fintype S] [Nonempty S] : mass (fun _ : S => True) = 1 := by
  unfold mass
  simp only [if_true]
  exact mean_const' 1

theorem mass_or_le {S : Type} [Fintype S] (E E' : S → Prop) :
    mass (fun s => E s ∨ E' s) ≤ mass E + mass E' := by
  unfold mass
  rw [← mean_add'']
  apply mean_mono'
  intro s
  by_cases h1 : E s <;> by_cases h2 : E' s <;> simp [h1, h2]

theorem mass_exists_le {S ι : Type} [Fintype S] [Fintype ι] (E : ι → S → Prop) :
    mass (fun s => ∃ i, E i s) ≤ ∑ i, mass (E i) := by
  unfold mass
  rw [← mean_sum']
  apply mean_mono'
  intro s
  by_cases h : ∃ i, E i s
  · rw [if_pos h]
    obtain ⟨i, hi⟩ := h
    have hle : (if E i s then (1 : ℚ) else 0) ≤ ∑ j, (if E j s then (1 : ℚ) else 0) :=
      Finset.single_le_sum (f := fun j => if E j s then (1 : ℚ) else 0)
        (fun j _ => ind_nonneg (E j s)) (Finset.mem_univ i)
    rw [if_pos hi] at hle
    exact hle
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun j _ => ind_nonneg (E j s))

/-- Union bound with a uniform per-index bound. -/
theorem mass_exists_le_card {S ι : Type} [Fintype S] [Fintype ι] (E : ι → S → Prop) (δ : ℚ)
    (h : ∀ i, mass (E i) ≤ δ) :
    mass (fun s => ∃ i, E i s) ≤ Fintype.card ι * δ := by
  refine (mass_exists_le E).trans ?_
  have hs := Finset.sum_le_card_nsmul Finset.univ (fun i => mass (E i)) δ (fun i _ => h i)
  simpa only [Finset.card_univ, nsmul_eq_mul] using hs

theorem mass_equiv {S T : Type} [Fintype S] [Fintype T] (e : S ≃ T) (E : S → Prop) :
    mass E = mass (fun t => E (e.symm t)) :=
  mean_equiv' e _

theorem mass_prod {R X : Type} [Fintype R] [Fintype X] (E : R × X → Prop) :
    mass E = mean (fun r => mass (fun x => E (r, x))) :=
  LawTransport.mean_product _

/-- A single point of a finite uniform coordinate. -/
theorem mass_point {U : Type} [Fintype U] (u₀ : U) :
    mass (fun u => u = u₀) = 1 / Fintype.card U := by
  simp [mass, mean]

/-! ### Conditioning on the other coordinates -/

/-- If `S ≃ R × X`, `D` depends only on `R`, and on every `r` with `D` the
`X`-mass of `E` is at most `δ`, then `mass (D ∧ E) ≤ mass D * δ`. -/
theorem mass_cond_le {S R X : Type} [Fintype S] [Fintype R] [Fintype X] [Nonempty X]
    (e : S ≃ R × X) (D E : S → Prop) (δ : ℚ) (hδ : 0 ≤ δ)
    (hD : ∀ r x x', D (e.symm (r, x)) → D (e.symm (r, x')))
    (hE : ∀ r x₀, D (e.symm (r, x₀)) → mass (fun x => E (e.symm (r, x))) ≤ δ) :
    mass (fun s => D s ∧ E s) ≤ mass D * δ := by
  have hl : mass (fun s => D s ∧ E s) =
      mean (fun r => mass (fun x => D (e.symm (r, x)) ∧ E (e.symm (r, x)))) := by
    rw [mass_equiv e, mass_prod]
  have hr : mass D = mean (fun r => mass (fun x => D (e.symm (r, x)))) := by
    rw [mass_equiv e, mass_prod]
  rw [hl, hr, ← mean_mul_const]
  apply mean_mono'
  intro r
  by_cases h : ∃ x₀, D (e.symm (r, x₀))
  · obtain ⟨x₀, hx₀⟩ := h
    have hall : ∀ x, D (e.symm (r, x)) := fun x => hD r x₀ x hx₀
    have h1 : mass (fun x => D (e.symm (r, x))) = 1 := by
      rw [mass_congr (fun x => D (e.symm (r, x))) (fun _ => True)
        (fun x => ⟨fun _ => trivial, fun _ => hall x⟩)]
      exact mass_true
    have h2 : mass (fun x => D (e.symm (r, x)) ∧ E (e.symm (r, x))) =
        mass (fun x => E (e.symm (r, x))) :=
      mass_congr _ _ (fun x => ⟨fun hx => hx.2, fun hx => ⟨hall x, hx⟩⟩)
    rw [h1, h2, one_mul]
    exact hE r x₀ hx₀
  · have h0 : mass (fun x => D (e.symm (r, x)) ∧ E (e.symm (r, x))) = 0 := by
      rw [mass_congr (fun x => D (e.symm (r, x)) ∧ E (e.symm (r, x))) (fun _ => False)
        (fun x => ⟨fun hx => h ⟨x, hx.1⟩, fun hx => hx.elim⟩)]
      exact mass_false
    rw [h0]
    exact mul_nonneg (mass_nonneg _) hδ

/-! ### First read against a designated field -/

/-- On `D`, the read `qa` does not move with the coordinate `u`; the address
`ga` determines `u` (its designated field). Then they agree on `D` with mass
at most `mass D / |U|`. -/
theorem hit_le {S R U A : Type} [Fintype S] [Fintype R] [Fintype U] [Nonempty U]
    (e : S ≃ R × U) (D : S → Prop) (qa ga : S → A) (π : R → A → U)
    (hD : ∀ r u u', D (e.symm (r, u)) → D (e.symm (r, u')))
    (hq : ∀ r u u', D (e.symm (r, u)) → qa (e.symm (r, u)) = qa (e.symm (r, u')))
    (hf : ∀ r u a, ga (e.symm (r, u)) = a → u = π r a) :
    mass (fun s => D s ∧ qa s = ga s) ≤ mass D * (1 / Fintype.card U) := by
  apply mass_cond_le e D (fun s => qa s = ga s) (1 / (Fintype.card U : ℚ)) (by positivity) hD
  intro r u₀ hu₀
  calc mass (fun u => qa (e.symm (r, u)) = ga (e.symm (r, u)))
      ≤ mass (fun u => u = π r (qa (e.symm (r, u₀)))) := by
        apply mass_mono
        intro u hu
        exact hf r u _ (hu.symm.trans (hq r u₀ u hu₀).symm)
    _ = 1 / Fintype.card U := mass_point _

/-- Collision of an address that does not move with `u` and one whose designated
field is `u`. -/
theorem pair_le {S R U A : Type} [Fintype S] [Fintype R] [Fintype U] [Nonempty U]
    (e : S ≃ R × U) (fa ga : S → A) (π : R → A → U)
    (hfa : ∀ r u u', fa (e.symm (r, u)) = fa (e.symm (r, u')))
    (hf : ∀ r u a, ga (e.symm (r, u)) = a → u = π r a) :
    mass (fun s => fa s = ga s) ≤ 1 / Fintype.card U := by
  have h := hit_le e (fun _ => True) fa ga π (fun _ _ _ _ => trivial)
    (fun r u u' _ => hfa r u u') hf
  calc mass (fun s => fa s = ga s) = mass (fun s => True ∧ fa s = ga s) :=
        mass_congr _ _ (fun s => ⟨fun hs => ⟨trivial, hs⟩, fun hs => hs.2⟩)
    _ ≤ mass (fun _ : S => True) * (1 / Fintype.card U) := h
    _ ≤ 1 * (1 / Fintype.card U) :=
        mul_le_mul_of_nonneg_right (mass_le_one _) (by positivity)
    _ = 1 / Fintype.card U := one_mul _

/-! ### The named freshness hypotheses -/

/-- Hit freshness of a charged read: there is a coordinate `u` of the coupling
space, of at least `Umin` values, that is the designated field of `ga`, while
the charging event `D` and the adversary read `qa` (on `D`) do not depend on it. -/
def HitFresh {S A : Type} [Fintype S] (D : S → Prop) (qa ga : S → A) (Umin : ℕ) : Prop :=
  ∃ (R U : Type) (_ : Fintype R) (_ : Fintype U) (_ : Nonempty U) (e : S ≃ R × U)
    (π : R → A → U),
    Umin ≤ Fintype.card U ∧
    (∀ r u u', D (e.symm (r, u)) → D (e.symm (r, u'))) ∧
    (∀ r u u', D (e.symm (r, u)) → qa (e.symm (r, u)) = qa (e.symm (r, u'))) ∧
    (∀ r u a, ga (e.symm (r, u)) = a → u = π r a)

/-- Pair freshness: the two addresses never coincide (structurally distinct), or
the second has a designated field on which the first does not depend. -/
def PairFresh {S A : Type} [Fintype S] (fa ga : S → A) (Umin : ℕ) : Prop :=
  (∀ s, fa s ≠ ga s) ∨
  ∃ (R U : Type) (_ : Fintype R) (_ : Fintype U) (_ : Nonempty U) (e : S ≃ R × U)
    (π : R → A → U),
    Umin ≤ Fintype.card U ∧
    (∀ r u u', fa (e.symm (r, u)) = fa (e.symm (r, u'))) ∧
    (∀ r u a, ga (e.symm (r, u)) = a → u = π r a)

theorem one_div_card_le {U : Type} [Fintype U] (Umin : ℕ) (hU : 0 < Umin)
    (hc : Umin ≤ Fintype.card U) : (1 : ℚ) / Fintype.card U ≤ 1 / Umin :=
  one_div_le_one_div_of_le (by exact_mod_cast hU) (by exact_mod_cast hc)

theorem hitFresh_mass {S A : Type} [Fintype S] (D : S → Prop) (qa ga : S → A) (Umin : ℕ)
    (hU : 0 < Umin) (hF : HitFresh D qa ga Umin) :
    mass (fun s => D s ∧ qa s = ga s) ≤ 1 / Umin := by
  obtain ⟨R, U, iR, iU, hne, e, π, hcard, hD, hq, hf⟩ := hF
  calc mass (fun s => D s ∧ qa s = ga s) ≤ mass D * (1 / Fintype.card U) :=
        hit_le e D qa ga π hD hq hf
    _ ≤ 1 * (1 / Fintype.card U) :=
        mul_le_mul_of_nonneg_right (mass_le_one D) (by positivity)
    _ = 1 / Fintype.card U := one_mul _
    _ ≤ 1 / Umin := one_div_card_le Umin hU hcard

theorem pairFresh_mass_one {S A : Type} [Fintype S] (fa ga : S → A) (Umin : ℕ)
    (hU : 0 < Umin) (hF : PairFresh fa ga Umin) :
    mass (fun s => fa s = ga s) ≤ 1 / Umin := by
  rcases hF with hne | ⟨R, U, iR, iU, hn, e, π, hcard, hfa, hf⟩
  · calc mass (fun s => fa s = ga s) ≤ mass (fun _ : S => False) :=
          mass_mono _ _ (fun s hs => hne s hs)
      _ = 0 := mass_false
      _ ≤ 1 / Umin := by positivity
  · exact (pair_le e fa ga π hfa hf).trans (one_div_card_le Umin hU hcard)

theorem pairFresh_mass {S A : Type} [Fintype S] (fa ga : S → A) (Umin : ℕ)
    (hU : 0 < Umin) (hF : PairFresh fa ga Umin ∨ PairFresh ga fa Umin) :
    mass (fun s => fa s = ga s) ≤ 1 / Umin := by
  rcases hF with h | h
  · exact pairFresh_mass_one fa ga Umin hU h
  · rw [mass_congr (fun s => fa s = ga s) (fun s => ga s = fa s) (fun s => eq_comm)]
    exact pairFresh_mass_one ga fa Umin hU h

/-! ### The assembled events -/

/-- Some charged prover position (a discarded attempt's read, or an unpublished
read of the accepted attempt) is read by the adversary. -/
def HitEv {S A : Type} (M q : ℕ) (charged : Fin M → S → Prop) (qry : Fin q → S → A)
    (addr : Fin M → S → A) (s : S) : Prop :=
  ∃ j i, charged j s ∧ qry i s = addr j s

/-- Two prover positions, at least one private, have the same address. -/
def CollEv {S A : Type} (M : ℕ) (priv : Fin M → Prop) (addr : Fin M → S → A) (s : S) : Prop :=
  ∃ j j', j < j' ∧ (priv j ∨ priv j') ∧ addr j s = addr j' s

/-- First-read union bound: `M` positions, `q` adversary reads. -/
theorem hitEv_mass_le {S A : Type} [Fintype S] (M q : ℕ) (charged : Fin M → S → Prop)
    (qry : Fin q → S → A) (addr : Fin M → S → A) (δ : ℚ)
    (h : ∀ j i, mass (fun s => charged j s ∧ qry i s = addr j s) ≤ δ) :
    mass (HitEv M q charged qry addr) ≤ M * q * δ := by
  have hu := mass_exists_le_card (ι := Fin M × Fin q)
    (fun p s => charged p.1 s ∧ qry p.2 s = addr p.1 s) δ (fun p => h p.1 p.2)
  calc mass (HitEv M q charged qry addr)
      ≤ mass (fun s => ∃ p : Fin M × Fin q, charged p.1 s ∧ qry p.2 s = addr p.1 s) :=
        mass_mono _ _ (fun s hs => by
          obtain ⟨j, i, hji⟩ := hs
          exact ⟨(j, i), hji⟩)
    _ ≤ Fintype.card (Fin M × Fin q) * δ := hu
    _ = M * q * δ := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
        push_cast
        ring

/-- Pair union bound over the ordered pairs of `M` positions. -/
theorem collEv_mass_le {S A : Type} [Fintype S] (M : ℕ) (priv : Fin M → Prop)
    (addr : Fin M → S → A) (δ : ℚ) (hδ : 0 ≤ δ)
    (h : ∀ j j', j < j' → (priv j ∨ priv j') → mass (fun s => addr j s = addr j' s) ≤ δ) :
    mass (CollEv M priv addr) ≤ M * M * δ := by
  have hp : ∀ p : Fin M × Fin M,
      mass (fun s => p.1 < p.2 ∧ (priv p.1 ∨ priv p.2) ∧ addr p.1 s = addr p.2 s) ≤ δ := by
    intro p
    by_cases hc : p.1 < p.2 ∧ (priv p.1 ∨ priv p.2)
    · calc mass (fun s => p.1 < p.2 ∧ (priv p.1 ∨ priv p.2) ∧ addr p.1 s = addr p.2 s)
          ≤ mass (fun s => addr p.1 s = addr p.2 s) := mass_mono _ _ (fun s hs => hs.2.2)
        _ ≤ δ := h p.1 p.2 hc.1 hc.2
    · calc mass (fun s => p.1 < p.2 ∧ (priv p.1 ∨ priv p.2) ∧ addr p.1 s = addr p.2 s)
          ≤ mass (fun _ : S => False) := mass_mono _ _ (fun s hs => hc ⟨hs.1, hs.2.1⟩)
        _ = 0 := mass_false
        _ ≤ δ := hδ
  have hu := mass_exists_le_card (ι := Fin M × Fin M)
    (fun p s => p.1 < p.2 ∧ (priv p.1 ∨ priv p.2) ∧ addr p.1 s = addr p.2 s) δ hp
  calc mass (CollEv M priv addr)
      ≤ mass (fun s => ∃ p : Fin M × Fin M,
          p.1 < p.2 ∧ (priv p.1 ∨ priv p.2) ∧ addr p.1 s = addr p.2 s) :=
        mass_mono _ _ (fun s hs => by
          obtain ⟨j, j', hjj⟩ := hs
          exact ⟨(j, j'), hjj⟩)
    _ ≤ Fintype.card (Fin M × Fin M) * δ := hu
    _ = M * M * δ := by
        rw [Fintype.card_prod, Fintype.card_fin]
        push_cast
        ring

/-- `HitEv` under per-read hit freshness. -/
theorem hitEv_mass_fresh {S A : Type} [Fintype S] (M q Umin : ℕ) (hU : 0 < Umin)
    (charged : Fin M → S → Prop) (qry : Fin q → S → A) (addr : Fin M → S → A)
    (hF : ∀ j i, HitFresh (charged j) (qry i) (addr j) Umin) :
    mass (HitEv M q charged qry addr) ≤ M * q / Umin := by
  have h := hitEv_mass_le M q charged qry addr (1 / Umin)
    (fun j i => hitFresh_mass (charged j) (qry i) (addr j) Umin hU (hF j i))
  calc mass (HitEv M q charged qry addr) ≤ M * q * (1 / Umin) := h
    _ = M * q / Umin := by ring

/-- `CollEv` under pair freshness of every private-involving pair. -/
theorem collEv_mass_fresh {S A : Type} [Fintype S] (M Umin : ℕ) (hU : 0 < Umin)
    (priv : Fin M → Prop) (addr : Fin M → S → A)
    (hF : ∀ j j', j < j' → (priv j ∨ priv j') →
      PairFresh (addr j) (addr j') Umin ∨ PairFresh (addr j') (addr j) Umin) :
    mass (CollEv M priv addr) ≤ M * M / Umin := by
  have h := collEv_mass_le M priv addr (1 / Umin) (by positivity)
    (fun j j' hj hp => pairFresh_mass (addr j) (addr j') Umin hU (hF j j' hj hp))
  calc mass (CollEv M priv addr) ≤ M * M * (1 / Umin) := h
    _ = M * M / Umin := by ring

#print axioms mean_equiv'
#print axioms mean_sum'
#print axioms mean_mul_const
#print axioms mass_nonneg
#print axioms mass_le_one
#print axioms mass_mono
#print axioms mass_congr
#print axioms mass_or_le
#print axioms mass_exists_le
#print axioms mass_exists_le_card
#print axioms mass_equiv
#print axioms mass_prod
#print axioms mass_point
#print axioms mass_cond_le
#print axioms hit_le
#print axioms pair_le
#print axioms hitFresh_mass
#print axioms pairFresh_mass
#print axioms hitEv_mass_le
#print axioms collEv_mass_le
#print axioms hitEv_mass_fresh
#print axioms collEv_mass_fresh
end R0Z.FsAbortBounds
