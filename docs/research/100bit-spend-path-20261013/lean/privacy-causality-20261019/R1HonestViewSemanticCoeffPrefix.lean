import R0Z.HonestView

set_option autoImplicit false
noncomputable section
namespace R0Z.HonestView
open R0P R0P.SemSource R0Z.MaskLayout R0Z.ViewAffine Polynomial
open AspisPool.AlgorithmicCircleDecoderV7 AspisWide.InitialEncoder
open AspisWide.Agreement AspisR0.Opening AspisR0.Chord AspisR0.ChordGeometry
open AspisV5ComponentCConcreteFoldLinearity
open AspisR0.PolynomialPair AspisR0.RoundNormalization AspisR0.Fold

/-- The round point used by the source builder only reads alpha challenges
strictly before the current round. -/
theorem roundPoint_prefix_eq
    {K : Type} [Field K]
    (j : Fin 10) (ch ch' : Challenges K)
    (hsem : ∀ k : Fin 25, k.val < 15 + j.val → ch.sem k = ch'.sem k)
    (z : K) (tail : Fin (9 - j.val) → Bool) :
    roundPoint ch j z tail = roundPoint ch' j z tail := by
  have halpha : ∀ q : Fin 10, q.val < j.val → alpha ch q = alpha ch' q := by
    intro q hq
    unfold alpha
    have hqBound : 15 + q.val < 25 := by have hj := j.isLt; omega
    have hqBefore : 15 + q.val < 15 + j.val := Nat.add_lt_add_left hq 15
    exact hsem ⟨15 + q.val, hqBound⟩ hqBefore
  funext q
  unfold roundPoint
  split_ifs with hlt heq
  · exact halpha q hlt
  · rfl
  · rfl
  all_goals rfl

/-- The actual typed-builder sumcheck coefficient in round `j` is determined
by the semantic challenges available before that round.  This is the
source-specific prefix law needed when `realAttempt` recomputes the view from
the larger transcript state: later alpha challenges do not rewrite an
already-built semantic row. -/
theorem run_semanticCoeff_prefix_stable
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10) (i : Fin 28)
    (ch ch' : Challenges K)
    (hsem : ∀ k : Fin 25, k.val < 15 + j.val → ch.sem k = ch'.sem k) :
    run (Bat := Bat) π pub B t ch r (.semanticCoeff j i) =
      run (Bat := Bat) π pub B t ch' r (.semanticCoeff j i) := by
  have hfixed (k : Fin 25) (hk : k.val < 15) : k.val < 15 + j.val :=
    Nat.lt_of_lt_of_le hk (Nat.le_add_right 15 j.val)
  have h0Fin : ch.sem ⟨0, by decide⟩ = ch'.sem ⟨0, by decide⟩ :=
    hsem ⟨0, by decide⟩ (hfixed _ (by decide))
  have h1Fin : ch.sem ⟨1, by decide⟩ = ch'.sem ⟨1, by decide⟩ :=
    hsem ⟨1, by decide⟩ (hfixed _ (by decide))
  have h2Fin : ch.sem ⟨2, by decide⟩ = ch'.sem ⟨2, by decide⟩ :=
    hsem ⟨2, by decide⟩ (hfixed _ (by decide))
  have h13Fin : ch.sem ⟨13, by decide⟩ = ch'.sem ⟨13, by decide⟩ :=
    hsem ⟨13, by decide⟩ (hfixed _ (by decide))
  have h14Fin : ch.sem ⟨14, by decide⟩ = ch'.sem ⟨14, by decide⟩ :=
    hsem ⟨14, by decide⟩ (hfixed _ (by decide))
  have h0 : ch.sem 0 = ch'.sem 0 := by simpa using h0Fin
  have h1 : ch.sem 1 = ch'.sem 1 := by simpa using h1Fin
  have hzc : zc ch = zc ch' := by
    funext q
    unfold zc
    have hq : q.val < 10 := q.isLt
    have hqSmall : 3 + q.val < 15 := by omega
    have hqBound : 3 + q.val < 25 := Nat.lt_trans hqSmall (by decide)
    have hqBefore : 3 + q.val < 15 + j.val :=
      Nat.lt_of_lt_of_le hqSmall (Nat.le_add_right 15 j.val)
    exact hsem ⟨3 + q.val, hqBound⟩ hqBefore
  have hprepare : prepare pub t ch = prepare pub t ch' := by
    funext c q
    unfold prepare
    by_cases hc : c.val = 26
    · simp only [if_pos hc]
      rw [h0, h1]
    · simp only [if_neg hc]
  change
    (Lagrange.interpolate Finset.univ (fun q : Fin 28 => (q.val : K))
      (fun q => ∑ tail : Fin (9 - j.val) → Bool,
        let a := roundPoint ch j (q.val : K) tail
        MaskedProtocol.terminalZ pub (ch.sem ⟨0, by omega⟩)
          (ch.sem ⟨1, by omega⟩) (ch.sem ⟨2, by omega⟩)
          (ch.sem ⟨13, by omega⟩) (ch.sem ⟨14, by omega⟩) (zc ch) B
          (honestClaims (applyAff B (prepare pub t ch) r) a)
          (R0P.Mask.honestExtra π (applyAff B (prepare pub t ch) r) a) a)).coeff i.val =
    (Lagrange.interpolate Finset.univ (fun q : Fin 28 => (q.val : K))
      (fun q => ∑ tail : Fin (9 - j.val) → Bool,
        let a := roundPoint ch' j (q.val : K) tail
        MaskedProtocol.terminalZ pub (ch'.sem ⟨0, by omega⟩)
          (ch'.sem ⟨1, by omega⟩) (ch'.sem ⟨2, by omega⟩)
          (ch'.sem ⟨13, by omega⟩) (ch'.sem ⟨14, by omega⟩) (zc ch') B
          (honestClaims (applyAff B (prepare pub t ch') r) a)
          (R0P.Mask.honestExtra π (applyAff B (prepare pub t ch') r) a) a)).coeff i.val
  apply congrArg (fun p : K[X] => p.coeff i.val)
  apply congrArg (fun f : Fin 28 → K =>
    Lagrange.interpolate Finset.univ (fun q : Fin 28 => (q.val : K)) f)
  funext q
  apply Finset.sum_congr rfl
  intro tail htail
  simp only [hprepare, h0Fin, h1Fin, h2Fin, h13Fin, h14Fin, hzc]
  rw [roundPoint_prefix_eq j ch ch' hsem (q.val : K) tail]

#print axioms roundPoint_prefix_eq
#print axioms run_semanticCoeff_prefix_stable

end R0Z.HonestView
