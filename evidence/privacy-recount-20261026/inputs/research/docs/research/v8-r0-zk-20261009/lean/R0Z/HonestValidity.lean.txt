import R0Z.IIPrimeResidual

/-! J0b (DESIGN-ii-prime §1.5, §4 J0b; LOG D36.4, D39.2): honest builds and
`HonestValid`.

Through the row-1023 lemma `laneOf_actual_zero`, `HonestValid pub B t ch` is a
statement about the prepared instance `prepare pub t ch` (lane 26 = the
literal helper of `t`):

* lanes 0..27 of `prepare pub t ch` are those of `t` (`laneOf_prepare_lt`);
* lane 28 (Copy) of `prepare pub t ch` vanishes at every active row whose four
  LogUp denominators `χ − value` are nonzero, for EVERY trace
  (`copyHolds_prepare`): the helper is then exactly the fraction sum;
* the two helper sums of `actual pub B t ch 0` are those of `helper pub t`
  (`actual_26`).

So `honestValid_of` derives `HonestValid` from the named builder properties
`HonestBuilderSound` (base typing, the 28 non-copy production lanes, the two
helper sums) and the challenge condition `NoPole`.

The pole is a genuine obstruction (`not_honestValid_of_pole`): at an active
row where `χ` equals a producer value, the Copy lane is
`−(χ−c₀)(χ−c₁)·pw₀·(χ−p₁)` whatever the helper, so `HonestValid` fails.  The
condition depends on the witness's tuple values, so `ValidOn P` (validity for
every `P`-challenge) cannot be derived for honest builds from builder
properties alone (`validOn_of_noPole` needs `NoPole` at every `P`-challenge).
Nothing here is assumed beyond the stated hypotheses. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.HonestValidity
open R0P R0P.Sumcheck R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12

attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### The prepared instance -/

theorem prepare_sem (pub : Public K) (t : Trace K) (ch : Challenges K) (c : Fin 16) (r : Fin 1024) :
    prepare pub t ch (Fin.castLE (by omega) c) r = t (Fin.castLE (by omega) c) r := by
  have hc : c.val ≠ 26 := by have := c.isLt; omega
  simp only [prepare, Fin.val_castLE, hc, ↓reduceIte]

theorem rowOpenings_prepare (pub : Public K) (t : Trace K) (ch : Challenges K) (b : Fin 1024) :
    rowOpenings (prepare pub t ch) b = rowOpenings t b := by
  simp only [rowOpenings, prepare_sem]

theorem copyEndpointTuple_prepare (pub : Public K) (t : Trace K) (ch : Challenges K) (tag : Nat)
    (ep : CopyEndpoint) :
    copyEndpointTuple (prepare pub t ch) tag ep = copyEndpointTuple t tag ep := by
  simp only [copyEndpointTuple, prepare_sem]

theorem copyRowValues_prepare (pub : Public K) (t : Trace K) (ch : Challenges K) (lam : K)
    (b : Fin 1024) (endpoint : CopyLink → CopyEndpoint) (slot : Fin 2) :
    copyRowValues (prepare pub t ch) lam b endpoint slot = copyRowValues t lam b endpoint slot := by
  simp only [copyRowValues, copyEndpointTuple_prepare]

theorem prepare_26 (pub : Public K) (t : Trace K) (ch : Challenges K) (b : Fin 1024) :
    prepare pub t ch 26 b = helper pub t (ch.sem 0) (ch.sem 1) b := by
  unfold prepare
  exact if_pos rfl

/-- Lanes 0..27 (Poseidon and the packed semantic families) read only the
semantic openings, so preparing H1 changes none of them. -/
theorem laneOf_prepare_lt (pub : Public K) (t : Trace K) (ch : Challenges K) (lam chi : K)
    (B : PackBasis F) (i : Fin 29) (bits : Fin 10 → Bool) (hi : i.val < 28) :
    laneOf (prepare pub t ch) pub lam chi B i bits = laneOf t pub lam chi B i bits := by
  unfold laneOf
  by_cases h4 : i.val < 4
  · simp only [dif_pos h4, rowOpenings_prepare]
  · simp only [dif_neg h4, dif_pos hi, semanticPackedLane, scalarLaneRow, rowOpenings_prepare]

/-- Lane 28 is the single Copy residual. -/
theorem laneOf_copy (t : Trace K) (pub : Public K) (lam chi : K) (B : PackBasis F)
    (bits : Fin 10 → Bool) :
    laneOf t pub lam chi B 28 bits =
      (copyFamily.residuals pub lam chi (rowOpenings t (rowOf bits)) (t 26 (rowOf bits))
        (rowSel (rowOf bits))).getD 0 0 := rfl

/-- H1 of the payload trace is the literal helper of the instance. -/
theorem actual_26 (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K) (r : Fin 1024) :
    PayloadSplit.actual pub B t ch 0 26 r = helper pub t (ch.sem 0) (ch.sem 1) r := by
  have h0 : (Sum.elim 0 (aff (0 : T K F)) : MaskTape K F) = 0 := by
    rw [map_zero (aff (K := K) (F := F))]
    funext z
    cases z <;> rfl
  unfold PayloadSplit.actual
  rw [R0Z.TerminalEligible.h1_applyAff, h0, R0Z.TerminalEligible.h1Padding_zero, Pi.zero_apply,
    add_zero, prepare_26]
  exact R0Z.HelperInvariant.helper_eligible pub t _ _ _ r

/-! ### The Copy lane away from poles -/

/-- No LogUp denominator of an active row vanishes at `χ`. -/
def NoPole (t : Trace K) (lam chi : K) : Prop :=
  ∀ b : Fin 1024, CopyActiveRow b → ∀ s : Fin 2,
    chi ≠ copyRowValues t lam b CopyLink.producer s ∧ chi ≠ copyRowValues t lam b CopyLink.consumer s

/-- Away from poles the Copy family holds on the prepared instance of EVERY trace. -/
theorem copyHolds_prepare (pub : Public K) (t : Trace K) (ch : Challenges K)
    (hnp : NoPole t (ch.sem 0) (ch.sem 1)) :
    CHolds copyFamily pub (ch.sem 0) (ch.sem 1) (prepare pub t ch) := by
  rw [copy_holds_iff]
  intro b hb
  dsimp only
  simp only [copyRowValues_prepare, prepare_26]
  obtain ⟨hp0, hc0⟩ := hnp b hb 0
  obtain ⟨hp1, hc1⟩ := hnp b hb 1
  have dp0 := sub_ne_zero.2 hp0
  have dp1 := sub_ne_zero.2 hp1
  have dc0 := sub_ne_zero.2 hc0
  have dc1 := sub_ne_zero.2 hc1
  simp only [helper, Fin.sum_univ_two]
  field_simp
  ring

/-! ### The builder properties and HonestValid -/

/-- J0b: the properties of an honest build that `HonestValid` needs, stated on
the raw instance trace.  `lanes` is ProductionHolds without the Copy family
(lanes 0..27 do not read λ, χ or H1); `helperSum` and `helperInactive` are the
two helper sums of the source terminal (Pair-forest terminal:1307–1308). -/
structure HonestBuilderSound (F : Subfield K) (pub : Public K) (B : PackBasis F) (t : Trace K) :
    Prop where
  baseTyped : BaseTyped F t
  lanes : ∀ (lam chi : K) (i : Fin 29) (b : Fin 10 → Bool), i.val < 28 → laneOf t pub lam chi B i b = 0
  helperSum : ∀ lam chi : K, ∑ r, helper pub t lam chi r = 0
  helperInactive : ∀ lam chi : K, ∑ r ∈ copyInactiveRows, helper pub t lam chi r = 0

/-- J0b: an honest build is valid at every pole-free challenge. -/
theorem honestValid_of (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K)
    (hs : HonestBuilderSound F pub B t) (hnp : NoPole t (ch.sem 0) (ch.sem 1)) :
    R0Z.HonestValid.HonestValid pub B t ch := by
  refine ⟨?_, ?_, ?_⟩
  · intro i b
    rw [R0Z.IIPrimeResidual.laneOf_actual_zero]
    by_cases hi : i.val < 28
    · rw [laneOf_prepare_lt pub t ch _ _ B i b hi]
      exact hs.lanes _ _ i b hi
    · obtain rfl : i = 28 := Fin.ext (by have := i.isLt; omega)
      rw [laneOf_copy]
      exact copyHolds_prepare pub t ch hnp (rowOf b) _ (List.mem_singleton_self _)
  · simp only [actual_26]
    exact hs.helperSum _ _
  · simp only [actual_26]
    exact hs.helperInactive _ _

/-- The prover-level form: honest instances of the statement. -/
def BuilderSoundOn (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle) : Prop :=
  ∀ w, h.public w = x.1 → HonestBuilderSound F x.1 B (h.build w)

theorem baseTyped_of (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (hs : BuilderSoundOn h B x) : ∀ w, h.public w = x.1 → BaseTyped F (h.build w) :=
  fun w hw => (hs w hw).baseTyped

/-- `ValidOn P` for an honest instance needs `NoPole` at every `P`-challenge. -/
theorem validOn_of_noPole (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) (hs : BuilderSoundOn h B x) (w : h.Instance)
    (hw : h.public w = x.1)
    (hnp : ∀ ch, P ch → NoPole (h.build w) (ch.sem 0) (ch.sem 1)) :
    R0Z.HonestValid.ValidOn P h B x w :=
  fun ch hP => honestValid_of x.1 B (h.build w) ch (hs w hw) (hnp ch hP)

/-! ### The pole obstruction -/

/-- At an active row with `χ` equal to producer value 0, `HonestValid` fails
unless `(χ−c₀)(χ−c₁)·pw₀·(χ−p₁) = 0`; the helper value plays no role. -/
theorem not_honestValid_of_pole (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K)
    (b : Fin 1024) (hb : CopyActiveRow b)
    (hχ : ch.sem 1 = copyRowValues t (ch.sem 0) b CopyLink.producer 0)
    (hne : ((ch.sem 1 - copyRowValues t (ch.sem 0) b CopyLink.consumer 0) *
        (ch.sem 1 - copyRowValues t (ch.sem 0) b CopyLink.consumer 1)) *
      (copyRowWeights pub b CopyLink.producer 0 *
        (ch.sem 1 - copyRowValues t (ch.sem 0) b CopyLink.producer 1)) ≠ 0) :
    ¬ R0Z.HonestValid.HonestValid pub B t ch := by
  intro hv
  have hC : CHolds copyFamily pub (ch.sem 0) (ch.sem 1) (prepare pub t ch) := by
    intro b' r hr
    rw [List.mem_singleton.1 hr]
    have h1 := hv.1 28 (rowBits b')
    rw [R0Z.IIPrimeResidual.laneOf_actual_zero, laneOf_copy, rowOf_rowBits] at h1
    exact h1
  have he := (copy_holds_iff pub (ch.sem 0) (ch.sem 1) (prepare pub t ch)).1 hC b hb
  dsimp only at he
  simp only [copyRowValues_prepare] at he
  rw [← hχ] at he
  simp only [sub_self, zero_mul, mul_zero, add_zero] at he
  exact hne he.symm

#print axioms prepare_sem
#print axioms rowOpenings_prepare
#print axioms copyEndpointTuple_prepare
#print axioms copyRowValues_prepare
#print axioms prepare_26
#print axioms laneOf_prepare_lt
#print axioms laneOf_copy
#print axioms actual_26
#print axioms NoPole
#print axioms copyHolds_prepare
#print axioms HonestBuilderSound
#print axioms honestValid_of
#print axioms BuilderSoundOn
#print axioms baseTyped_of
#print axioms validOn_of_noPole
#print axioms not_honestValid_of_pole
end R0Z.HonestValidity
