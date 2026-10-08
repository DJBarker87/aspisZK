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
over the ≤ 100 candidates (`candidates`: the joint list of the committed words with the
C2 words of the prefix, or, before C2, of the padded words) of G13′'s
per-candidate round set, so its cardinality is ≤ 100·`semRoundBudget i`
and its sampler mass is
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

/-- The candidate traces at a semantic round: before the C2 message (rounds
0 and 1) the joint list of the committed C1 words padded by the zero
codeword at lanes 26/27, restricted to zero messages there; at round 2 the
list of the words with the current C2 message; afterwards the list of the
words with the prefix's C2 message. Malformed prefixes have no candidates. -/
def candidates (x : TypedContext K Sfield) (rounds : List (Msg K K (SemMsg K) × Chal K K))
    (sm : SemMsg K) : Finset (Trace K) :=
  if rounds.length < 2 then
    (Lambda (c2Words x padWord padWord)).filter (fun t => t 26 = 0 ∧ t 27 = 0)
  else if rounds.length = 2 then
    match sm with
    | .h1 h g => Lambda (c2Words x h g)
    | _ => ∅
  else
    match c2Of rounds with
    | some (h, g) => Lambda (c2Words x h g)
    | Option.none => ∅

attribute [local irreducible] Lambda

theorem candidates_card (x : TypedContext K Sfield)
    (rounds : List (Msg K K (SemMsg K) × Chal K K)) (sm : SemMsg K) :
    (candidates x rounds sm).card ≤ 100 := by
  classical
  unfold candidates
  split_ifs
  · exact (Finset.card_filter_le _ _).trans (Lambda_card _)
  · cases sm with
    | none => simp
    | h1 h g => exact Lambda_card _
    | roundPoly p => simp
  · cases hc : c2Of rounds with
    | none => simp
    | some p =>
      rcases p with ⟨h, g⟩
      exact Lambda_card _

/-- The round polynomials visible at a round: the prefix's `roundPoly`
messages at rounds 14 + j, the current message at the current round. -/
def polysOf (rounds : List (Msg K K (SemMsg K) × Chal K K)) (sm : SemMsg K) :
    Fin 10 → K[X] := fun j =>
  if h : 14 + j.val < rounds.length then
    match (rounds[14 + j.val]'h).1 with
    | .semantic (.roundPoly p) => p
    | _ => 0
  else if 14 + j.val = rounds.length then
    match sm with
    | .roundPoly p => p
    | _ => 0
  else 0

/-- The verifier's degree check on the current round polynomial. -/
def degreeOK : SemMsg K → Prop
  | .roundPoly p => p.natDegree ≤ 27
  | _ => True

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem degreeChecked_of_degreeOK (rounds : List (Msg K K (SemMsg K) × Chal K K))
    (sm : SemMsg K) (hok : degreeOK sm) (h : rounds.length < 24)
    (pref : Fin rounds.length → K) :
    semRoundDegreeChecked (fixedStrat (polysOf rounds sm)) ⟨rounds.length, h⟩ pref := by
  unfold semRoundDegreeChecked
  split
  · rename_i h14
    have h14' : 14 ≤ rounds.length := h14
    simp only [fixedStrat, polysOf]
    have hidx : 14 + (rounds.length - 14) = rounds.length := by omega
    rw [dif_neg (by omega), if_pos hidx]
    cases sm with
    | none => simp
    | h1 a b => simp
    | roundPoly p => exact hok
  · trivial

/-- B2's `semanticBad` for the pair forest: with the prefix's challenges
`cs` and its C2 words, some candidate is bad at the current round. A current
round polynomial of degree > 27 is rejected by the verifier and is not a
bad event. -/
def semanticBad {F : Subfield K} (B : PackBasis F)
    (P : Prefix K K (TypedContext K Sfield) (SemMsg K)) (sm : SemMsg K) (c : K) : Prop :=
  ∃ (h : P.rounds.length < 24) (cs : List K), semChals P.rounds = some cs ∧ degreeOK sm ∧
    ∃ t ∈ candidates P.statement P.rounds sm,
      semRoundBad t P.statement.pub B (fun pre => virtualPoly P.statement.pub B t pre)
        (fixedStrat (polysOf P.rounds sm)) ⟨P.rounds.length, h⟩ (fun j => cs.getD j.val 0) c

theorem semanticBad_card {F : Subfield K} (B : PackBasis F)
    (P : Prefix K K (TypedContext K Sfield) (SemMsg K)) (sm : SemMsg K)
    (h : P.rounds.length < 24) :
    (Finset.univ.filter (semanticBad B P sm)).card ≤
      100 * semRoundBudget (⟨P.rounds.length, h⟩ : Fin 24) := by
  classical
  by_cases hcs : ∃ cs, semChals P.rounds = some cs
  swap
  · have hempty : Finset.univ.filter (semanticBad B P sm) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro c _ ⟨_, cs, hc, _⟩
      exact hcs ⟨cs, hc⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  by_cases hok : degreeOK sm
  swap
  · have hempty : Finset.univ.filter (semanticBad B P sm) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro c _ ⟨_, _, _, hd, _⟩
      exact hok hd
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  obtain ⟨cs, hcs⟩ := hcs
  let pref : Fin P.rounds.length → K := fun j => cs.getD j.val 0
  let per : Trace K → Finset K := fun t => Finset.univ.filter
    (semRoundBad t P.statement.pub B (fun pre => virtualPoly P.statement.pub B t pre)
      (fixedStrat (polysOf P.rounds sm)) ⟨P.rounds.length, h⟩ pref)
  have hsub : Finset.univ.filter (semanticBad B P sm) ⊆
      (candidates P.statement P.rounds sm).biUnion per := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, semanticBad] at hc
    obtain ⟨_, cs', hcs', _, t, ht, hb⟩ := hc
    have hcs'' : cs' = cs := Option.some.inj (hcs'.symm.trans hcs)
    subst hcs''
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, per]
    exact ⟨t, ht, hb⟩
  have hper : ∀ t ∈ candidates P.statement P.rounds sm, (per t).card ≤ semRoundBudget (⟨P.rounds.length, h⟩ : Fin 24) := by
    intro t _
    exact semRoundBad_card t P.statement.pub B (fun pre => virtualPoly P.statement.pub B t pre)
      (fixedStrat (polysOf P.rounds sm)) (⟨P.rounds.length, h⟩ : Fin 24) pref
      (degreeChecked_of_degreeOK P.rounds sm hok h pref)
  calc (Finset.univ.filter (semanticBad B P sm)).card
      ≤ ((candidates P.statement P.rounds sm).biUnion per).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ candidates P.statement P.rounds sm, (per t).card := Finset.card_biUnion_le
    _ ≤ (candidates P.statement P.rounds sm).card • semRoundBudget (⟨P.rounds.length, h⟩ : Fin 24) :=
        Finset.sum_le_card_nsmul _ _ _ hper
    _ = (candidates P.statement P.rounds sm).card * semRoundBudget (⟨P.rounds.length, h⟩ : Fin 24) :=
        smul_eq_mul _ _
    _ ≤ 100 * semRoundBudget (⟨P.rounds.length, h⟩ : Fin 24) :=
        Nat.mul_le_mul_right _ (candidates_card _ _ _)

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
theorem semantic_round_density {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact}
    (B : PackBasis F) (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact))
    (sm : SemMsg WideExact) (h : Q.rounds.length < 24) :
    mean (fun s : State => indicator (semanticBad B Q sm (semChal s))) ≤
      (1 + deltaQ) * ((100 * semRoundBudget (⟨Q.rounds.length, h⟩ : Fin 24) : Nat) / (P ^ 4 : ℚ)) := by
  classical
  let bad : Finset WideExact := Finset.univ.filter (semanticBad B Q sm)
  have hmem : ∀ s : State, semanticBad B Q sm (semChal s) ↔ semChal s ∈ bad := by
    intro s
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcard : (bad.card : ℚ) ≤ (100 * semRoundBudget (⟨Q.rounds.length, h⟩ : Fin 24) : Nat) := by
    exact_mod_cast semanticBad_card B Q sm h
  calc mean (fun s : State => indicator (semanticBad B Q sm (semChal s)))
      = mean (fun s : State => indicator (semChal s ∈ bad)) := by
        apply mean_congr
        intro s
        exact indicator_iff (hmem s)
    _ ≤ bad.card * ((1 + deltaQ) / (P ^ 4 : ℚ)) := semChal_event bad
    _ ≤ (100 * semRoundBudget (⟨Q.rounds.length, h⟩ : Fin 24) : Nat) * ((1 + deltaQ) / (P ^ 4 : ℚ)) := by
        apply mul_le_mul_of_nonneg_right hcard
        apply div_nonneg
        · linarith [deltaQ_nonneg]
        · positivity
    _ = (1 + deltaQ) * ((100 * semRoundBudget (⟨Q.rounds.length, h⟩ : Fin 24) : Nat) / (P ^ 4 : ℚ)) := by ring

#print axioms candidates_card
#print axioms semanticBad_card
#print axioms qm31Sample_mass_slack
#print axioms semChal_event
#print axioms semantic_round_density
end
end R0P.SemSource
