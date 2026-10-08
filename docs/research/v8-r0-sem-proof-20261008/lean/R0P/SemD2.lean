import R0P.SemD3
import R0C.ModuloField
import R0C.ConcreteSlack

/-! Lead: D2 rows for the 24 semantic rounds.

Each semantic challenge is `challenge_qm31` (aspis-core transcript.rs:378,
four accepted limbs < P, embedded in the wide field E for the SEM
objects). As for the opening layer's `R0C.ModuloField.ordinary`, the
sampler is modelled by the rejection-free reduction of one 32-byte duplex
block modulo P⁴ (the retained canonical retry implementation's law bridge
is the same open item recorded in the close job's FS_LOG). Per-element
mass ≤ 1/P⁴ + 1/256³² = (1+δ_q)/P⁴ with δ_q = P⁴/256³² < 2⁻¹³¹.

For round i with the earlier challenges fixed, the bad set is the union
over the ≤ 100 candidates of `Lambda x.W` of G13′'s per-candidate round set,
so its cardinality is ≤ 100·`semRoundBudget i` and its sampler mass is
≤ (1+δ_q)·100·`semRoundBudget i`/P⁴: the per-row content of FS2.D2 for the
semantic rounds, assembled into the protocol instance by G16. -/
set_option autoImplicit false
namespace R0P.SemSource
open FS FS2 R0C.SemStatement Polynomial Sumcheck
open AspisR0.ListsResponses AspisV8R19.MemoizedProgramLaw
open R0C.ModuloField R0C.ModuloCounting AspisV8R19.R599CanonicalFieldTuple
open AspisWideTower AspisCircleGroupOrder
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound

noncomputable section
attribute [local instance] Classical.propDecidable

section Generic
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {Sfield : Fin 29 → Subfield K}

/-- The round-i bad set of the public context, as a predicate on the fresh
challenge `c`, with the earlier challenges `pref` fixed. -/
def semanticBadRound (x : TypedContext K Sfield) {F : Subfield K} (B : PackBasis F)
    (polys : Fin 10 → K[X]) (i : Fin 24) (pref : Fin i.val → K) (c : K) : Prop :=
  ∃ t ∈ Lambda x.W, semRoundBad t x.pub B (fun pre => virtualPoly x.pub B t pre)
    (fixedStrat polys) i pref c

attribute [local irreducible] Lambda

theorem semanticBadRound_card (x : TypedContext K Sfield) {F : Subfield K} (B : PackBasis F)
    (polys : Fin 10 → K[X]) (i : Fin 24) (pref : Fin i.val → K)
    (hchecked : semRoundDegreeChecked (fixedStrat polys) i pref) :
    (Finset.univ.filter (semanticBadRound x B polys i pref)).card ≤ 100 * semRoundBudget i := by
  classical
  let per : Trace K → Finset K := fun t => Finset.univ.filter
    (semRoundBad t x.pub B (fun pre => virtualPoly x.pub B t pre) (fixedStrat polys) i pref)
  have hsub : Finset.univ.filter (semanticBadRound x B polys i pref) ⊆ (Lambda x.W).biUnion per := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, semanticBadRound] at hc
    obtain ⟨t, ht, hb⟩ := hc
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, per]
    exact ⟨t, ht, hb⟩
  have hper : ∀ t ∈ Lambda x.W, (per t).card ≤ semRoundBudget i := by
    intro t _
    exact semRoundBad_card t x.pub B _ _ i pref hchecked
  calc (Finset.univ.filter (semanticBadRound x B polys i pref)).card
      ≤ ((Lambda x.W).biUnion per).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ Lambda x.W, (per t).card := Finset.card_biUnion_le
    _ ≤ (Lambda x.W).card • semRoundBudget i := Finset.sum_le_card_nsmul _ _ _ hper
    _ = (Lambda x.W).card * semRoundBudget i := smul_eq_mul _ _
    _ ≤ 100 * semRoundBudget i := Nat.mul_le_mul_right _ (Lambda_card x.W)

end Generic

/-! ## The QM31 challenge sampler -/

/-- Base-P positional rank of a four-limb QM31 element. -/
def qm31Rank : Fin (P ^ 4) ≃ AspisV5ComponentCQM31TowerExact.QM31Exact := finFunctionFinEquiv.symm.trans tupleFieldEquiv

/-- The rejection-free model of `challenge_qm31` on one duplex block. -/
def qm31Sample (s : State) : AspisV5ComponentCQM31TowerExact.QM31Exact :=
  qm31Rank (R0C.ModuloCounting.reduce (by norm_num [P]) (blockRank s))

theorem qm31Sample_mass (y : AspisV5ComponentCQM31TowerExact.QM31Exact) :
    mean (fun s => indicator (qm31Sample s = y)) ≤ 1 / (P ^ 4 : ℚ) + 1 / (256 ^ 32 : ℚ) := by
  simpa only [qm31Sample, Nat.cast_pow, Nat.cast_ofNat] using
    R0C.ModuloCounting.encoded_mass_slack (by positivity : 0 < 256 ^ 32)
      (by norm_num [P] : 0 < P ^ 4) blockRank qm31Rank y

/-- The slack of the rejection-free model relative to the ideal 1/P⁴. -/
def deltaQ : ℚ := (P ^ 4 : ℚ) / (256 ^ 32 : ℚ)

theorem deltaQ_nonneg : 0 ≤ deltaQ := by unfold deltaQ; positivity

theorem deltaQ_small : deltaQ ≤ 1 / 2 ^ 131 := by norm_num [deltaQ, P]

theorem qm31Sample_mass_slack (y : AspisV5ComponentCQM31TowerExact.QM31Exact) :
    mean (fun s => indicator (qm31Sample s = y)) ≤ (1 + deltaQ) / (P ^ 4 : ℚ) := by
  refine (qm31Sample_mass y).trans (le_of_eq ?_)
  unfold deltaQ
  field_simp

/-- The challenge in the wide field. -/
def semChal (s : State) : WideExact := algebraMap AspisV5ComponentCQM31TowerExact.QM31Exact WideExact (qm31Sample s)

theorem semChal_mass (y : WideExact) :
    mean (fun s => indicator (semChal s = y)) ≤ (1 + deltaQ) / (P ^ 4 : ℚ) := by
  by_cases hy : ∃ q : AspisV5ComponentCQM31TowerExact.QM31Exact, algebraMap AspisV5ComponentCQM31TowerExact.QM31Exact WideExact q = y
  · obtain ⟨q, rfl⟩ := hy
    have he : ∀ s, (semChal s = algebraMap AspisV5ComponentCQM31TowerExact.QM31Exact WideExact q) ↔ qm31Sample s = q := by
      intro s
      exact (algebraMap AspisV5ComponentCQM31TowerExact.QM31Exact WideExact).injective.eq_iff
    rw [mean_congr (fun s => indicator_iff (he s))]
    exact qm31Sample_mass_slack q
  · have he : ∀ s, (semChal s = y) ↔ False := by
      intro s
      exact iff_false_intro (fun h => hy ⟨qm31Sample s, h⟩)
    rw [mean_congr (fun s => indicator_iff (he s)), indicator_false, mean_const]
    apply div_nonneg
    · linarith [deltaQ_nonneg]
    · positivity

theorem semChal_event (bad : Finset WideExact) :
    mean (fun s => indicator (semChal s ∈ bad)) ≤ bad.card * ((1 + deltaQ) / (P ^ 4 : ℚ)) :=
  R0C.ModuloCounting.event_mass_le semChal _ semChal_mass bad

/-- The sampler mass of a semantic round's bad set. -/
theorem semantic_round_density {Sfield : Fin 29 → Subfield WideExact}
    (x : TypedContext WideExact Sfield) {F : Subfield WideExact} (B : PackBasis F)
    (polys : Fin 10 → WideExact[X]) (i : Fin 24) (pref : Fin i.val → WideExact)
    (hchecked : semRoundDegreeChecked (fixedStrat polys) i pref) :
    mean (fun s : State => indicator (semanticBadRound x B polys i pref (semChal s))) ≤
      (1 + deltaQ) * ((100 * semRoundBudget i : Nat) / (P ^ 4 : ℚ)) := by
  classical
  let bad : Finset WideExact := Finset.univ.filter (semanticBadRound x B polys i pref)
  have hmem : ∀ s : State, semanticBadRound x B polys i pref (semChal s) ↔ semChal s ∈ bad := by
    intro s
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcard : (bad.card : ℚ) ≤ (100 * semRoundBudget i : Nat) := by
    exact_mod_cast semanticBadRound_card x B polys i pref hchecked
  calc mean (fun s : State => indicator (semanticBadRound x B polys i pref (semChal s)))
      = mean (fun s : State => indicator (semChal s ∈ bad)) := by
        apply mean_congr
        intro s
        exact indicator_iff (hmem s)
    _ ≤ bad.card * ((1 + deltaQ) / (P ^ 4 : ℚ)) := semChal_event bad
    _ ≤ (100 * semRoundBudget i : Nat) * ((1 + deltaQ) / (P ^ 4 : ℚ)) := by
        apply mul_le_mul_of_nonneg_right hcard
        apply div_nonneg
        · linarith [deltaQ_nonneg]
        · positivity
    _ = (1 + deltaQ) * ((100 * semRoundBudget i : Nat) / (P ^ 4 : ℚ)) := by ring

#print axioms semanticBadRound_card
#print axioms qm31Sample_mass_slack
#print axioms semChal_event
#print axioms semantic_round_density
end
end R0P.SemSource
