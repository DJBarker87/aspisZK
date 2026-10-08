import R0P.SemDecision
import R0P.SemRounds
import R0P.SemClosed

/-! Lead: the D3 core for the semantic rounds.

For a candidate trace t with honest claims, the virtual polynomial is the
terminal at the honest claims; the B2 round classifier is G13′'s
`semRoundBad` for some candidate of `Lambda x.W`. `d3_core`: if the parsed
semantic transcript passes `sumcheckChecks` with honest claims for a
candidate t of the typed words, and no semantic round is bad for t, then
t satisfies every production family and the links balance, hence the
payment witness exists. The three bridge facts of G14′ (honest terminal at
Boolean rows, weighted-degree bound, and the round checks as `accept`) are
named hypotheses. -/
set_option autoImplicit false
namespace R0P.SemSource
open FS FS2 R0C.SemStatement Polynomial Sumcheck
open AspisPool.AlgorithmicCircleDecoderV7 AspisV8R19.MemoizedProgramLaw
open AspisR0.Chord AspisR0.ChordGeometry AspisR0.Opening AspisR0.ListsResponses AspisR0.LinearDual

noncomputable section
attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {Sfield : Fin 29 → Subfield K}

/-- Honest claims of a trace at the three opening points of `v`. -/
def honestClaims (t : Trace K) (v : Fin 10 → K) : Fin 3 → Fin 29 → K :=
  fun j l => dot (eqWeight (openingPoints v j)) (t l)

/-- The 14 pre-sumcheck challenges: λ, χ, θ, zc₀..zc₉, μ. -/
def preZc (pre : Fin 14 → K) : Fin 10 → K := fun j => pre ⟨3 + j.val, by omega⟩

/-- The virtual polynomial of candidate t: the terminal at its honest claims. -/
def virtualPoly (pub : Public K) {F : Subfield K} (B : PackBasis F) (t : Trace K)
    (pre : Fin 14 → K) : (Fin 10 → K) → K :=
  fun v => terminalValue pub (pre 0) (pre 1) (pre 2) (pre 13) (preZc pre) B (honestClaims t v) v

/-- G14′ item 4: at a Boolean row the honest terminal is the batched row value. -/
def HonestRows (pub : Public K) {F : Subfield K} (B : PackBasis F) (t : Trace K) : Prop :=
  ∀ (pre : Fin 14 → K) (b : Fin 10 → Bool),
    virtualPoly pub B t pre (ofBool b) =
      eqwB 10 (preZc pre) b * lanesComp (pre 2) (laneOf t pub (pre 0) (pre 1) B) b +
      pre 13 * t 26 (rowOf b) +
      (pre 13) ^ 2 * ((1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b))

/-- G14′ item 5: weighted individual degree ≤ 27. -/
def VirtualDeg (pub : Public K) {F : Subfield K} (B : PackBasis F) (t : Trace K) : Prop :=
  ∀ pre : Fin 14 → K, IndDeg 27 10 (virtualPoly pub B t pre)

/-- G14′ item 6: the round checks with honest final claims are `accept`,
for the challenge vector `r` (λ, χ, θ, zc, μ at 0–13; α at 14–23). -/
def ChecksAccept (pub : Public K) {F : Subfield K} (B : PackBasis F) (t : Trace K) : Prop :=
  ∀ (r : Fin 24 → K) (polys : Fin 10 → K[X]),
    sumcheckChecks pub B (List.ofFn r) List.length_ofFn polys (honestClaims t (semSlice r 14 10)) →
      accept 27 10 (virtualPoly pub B t (semSlice r 0 14)) 0 polys (semSlice r 14 10)

/-- The prover's polynomials as a constant strategy (the transcript is fixed). -/
def fixedStrat (polys : Fin 10 → K[X]) :
    (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X] :=
  fun _ j _ => polys j

/-- G13′'s classifier for one candidate, over the 24 challenges `r`. -/
def candidateRoundBad (pub : Public K) {F : Subfield K} (B : PackBasis F) (t : Trace K)
    (polys : Fin 10 → K[X]) (r : Fin 24 → K) (i : Fin 24) : Prop :=
  semRoundBad t pub B (fun pre => virtualPoly pub B t pre) (fixedStrat polys) i (semPrefix r i) (r i)

/-- B2's `semanticBad` at round i: some candidate of the committed words is bad. -/
def semanticBadAt (x : TypedContext K Sfield) {F : Subfield K} (B : PackBasis F)
    (polys : Fin 10 → K[X]) (r : Fin 24 → K) (i : Fin 24) : Prop :=
  ∃ t ∈ Lambda x.W, candidateRoundBad x.pub B t polys r i

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem strategyPolys_fixed (polys : Fin 10 → K[X]) (pre : Fin 14 → K) (α : Fin 10 → K) :
    SemBadSets.strategyPolys (fixedStrat polys pre) α = polys := by
  funext j
  rfl

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem semSlice_zero_apply (r : Fin 24 → K) (j : Fin 14) :
    semSlice r 0 14 j = r ⟨j.val, by omega⟩ := by
  simp only [semSlice, semPrefixVal, Nat.zero_add]
  rw [dif_pos (by omega)]

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem preZc_semSlice (r : Fin 24 → K) : preZc (semSlice r 0 14) = semSlice r 3 10 := by
  funext j
  simp only [preZc, semSlice, semPrefixVal, Nat.zero_add]

omit [Fintype K] [DecidableEq K] in
/-- The D3 core. -/
theorem d3_core (P : Nat) [CharP K P] (hP : P = 2 ^ 31 - 1)
    (F : Subfield K) (B : PackBasis F) (x : TypedContext K Sfield) (t : Trace K)
    (hA : BaseTyped F t) (hpub : PublicBase F x.pub)
    (hrows : HonestRows x.pub B t) (hdeg : VirtualDeg x.pub B t) (hchk : ChecksAccept x.pub B t)
    (r : Fin 24 → K) (polys : Fin 10 → K[X])
    (hsum : sumcheckChecks x.pub B (List.ofFn r) List.length_ofFn polys
      (honestClaims t (semSlice r 14 10)))
    (hgood : ∀ i : Fin 24, ¬ candidateRoundBad x.pub B t polys r i) :
    ProductionHolds x.pub (r 0) (r 1) t ∧ CopyLinkBalance x.pub t := by
  have hacc := hchk r polys hsum
  have hacc' : accept 27 10 (virtualPoly x.pub B t (semSlice r 0 14)) 0
      (SemBadSets.strategyPolys (fixedStrat polys (semSlice r 0 14)) (semSlice r 14 10))
      (semSlice r 14 10) := by
    rw [strategyPolys_fixed]
    exact hacc
  have hG : ∀ b, virtualPoly x.pub B t (semSlice r 0 14) (ofBool b) =
      eqwB 10 (semSlice r 3 10) b * lanesComp (r 2) (laneOf t x.pub (r 0) (r 1) B) b +
      r 13 * t 26 (rowOf b) +
      (r 13) ^ 2 * ((1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b)) := by
    intro b
    rw [hrows, preZc_semSlice, semSlice_zero_apply, semSlice_zero_apply, semSlice_zero_apply,
      semSlice_zero_apply]
    rfl
  exact semantic_sound_rounds P hP F B x.pub t hA hpub r (fun pre => virtualPoly x.pub B t pre)
    (fixedStrat polys) hG (hdeg _) hacc' hgood

#print axioms strategyPolys_fixed
#print axioms d3_core
end
end R0P.SemSource
