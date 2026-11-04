import R1Z.PhaseBuilderDependenciesBin

/-! Symbolic message-prefix facts about the existing honest-view model.
No Boolean-tail sum, interpolation table or coefficient universe is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseMessageDependenciesBin
open R0P R0P.SemSource R0Z R0Z.HonestView R0Z.MaskLayout R1Z.Batched
  R1Z.PhaseBuilderDependenciesBin

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

def SemPrefix (n : ℕ) (ch ch' : Challenges K) : Prop :=
  ∀ i : Fin 25, i.val < n → ch.sem i = ch'.sem i

theorem roundPoint_prefix (ch ch' : Challenges K) (j : Fin 10)
    (he : SemPrefix (15 + j.val) ch ch') (z : K) (tail : Fin (9-j.val) → Bool) :
    roundPoint ch j z tail = roundPoint ch' j z tail := by
  funext i
  unfold roundPoint
  split
  · exact he _ (by dsimp [alpha]; omega)
  · rfl

theorem zc_prefix (ch ch' : Challenges K) (n : ℕ) (hn : 13 ≤ n)
    (he : SemPrefix n ch ch') : zc ch = zc ch' := by
  funext i
  exact he ⟨3 + i.val, by omega⟩ (by dsimp; omega)

/-- Actual semantic coefficient cells use only the preceding semantic rows. -/
theorem semanticCoeff_prefix (π : Fin 1024 ≃ Fin 1024) (pub : Public K)
    (B : PackBasis F) (t : Trace K) (r : AffTape K F)
    (ch ch' : Challenges K) (j : Fin 10) (i : Fin 28)
    (he : SemPrefix (15 + j.val) ch ch') :
    run (Bat := R1Bat) π pub B t ch r (.semanticCoeff j i) =
      run (Bat := R1Bat) π pub B t ch' r (.semanticCoeff j i) := by
  have h0 := he 0 (by omega)
  have h1 := he 1 (by omega)
  have h2 := he 2 (by omega)
  have h13 := he 13 (by omega)
  have h14 := he 14 (by omega)
  have hz := zc_prefix ch ch' (15 + j.val) (by omega) he
  have hp : ∀ z tail, roundPoint ch j z tail = roundPoint ch' j z tail :=
    roundPoint_prefix ch ch' j he
  simp only [run, prepare_local pub t ch ch' h0 h1, hp, h0, h1, h2, h13, h14, hz]

/-- The same prefix fact for the semantic polynomial, before coefficient reads. -/
theorem roundPoly_prefix (π : Fin 1024 ≃ Fin 1024) (pub : Public K)
    (B : PackBasis F) (t : Trace K) (r : AffTape K F)
    (ch ch' : Challenges K) (j : Fin 10)
    (he : SemPrefix (15 + j.val) ch ch') :
    roundPoly π pub B t ch j r = roundPoly π pub B t ch' j r := by
  rw [roundPoly_apply, roundPoly_apply]
  have hz := zc_prefix ch ch' (15 + j.val) (by omega) he
  simp only [roundPoint_prefix ch ch' j he, he 0 (by omega), he 1 (by omega),
    he 2 (by omega), he 13 (by omega), he 14 (by omega), hz]

theorem batch_prefix (π : Fin 1024 ≃ Fin 1024) (ch ch' : Challenges K)
    (hg : ch.opening 0 = ch'.opening 0) : batchR1 π ch = batchR1 π ch' := by
  simp only [batchR1, hg]

theorem weights_prefix (π : Fin 1024 ≃ Fin 1024) (ch ch' : Challenges K)
    (hs : ch.sem = ch'.sem) (hc : ch.circle = ch'.circle)
    (hk : ch.opening 1 = ch'.opening 1) : weightsR1 π ch = weightsR1 π ch' := by
  have ha : R0Z.HonestView.alpha ch = R0Z.HonestView.alpha ch' := by
    unfold R0Z.HonestView.alpha
    rw [hs]
  unfold weightsR1 ell
  rw [hk, ha, hc]

theorem round0_prefix (π : Fin 1024 ≃ Fin 1024) (ch ch' : Challenges K)
    (t : Trace K) (i : Fin 7) (hs : ch.sem = ch'.sem) (hc : ch.circle = ch'.circle)
    (hg : ch.opening 0 = ch'.opening 0) (hk : ch.opening 1 = ch'.opening 1) :
    BatchedLayer.read π ch t (.round0 i : R1Bat) =
      BatchedLayer.read π ch' t (.round0 i : R1Bat) := by
  rw [read_round0, read_round0, batch_prefix π ch ch' hg, weights_prefix π ch ch' hs hc hk]

theorem round1_prefix (π : Fin 1024 ≃ Fin 1024) (ch ch' : Challenges K)
    (t : Trace K) (i : Fin 7) (hs : ch.sem = ch'.sem) (hc : ch.circle = ch'.circle)
    (hg : ch.opening 0 = ch'.opening 0) (hk : ch.opening 1 = ch'.opening 1)
    (ha : ch.opening 2 = ch'.opening 2) :
    BatchedLayer.read π ch t (.round1 i : R1Bat) =
      BatchedLayer.read π ch' t (.round1 i : R1Bat) := by
  rw [read_round1, read_round1, q1_local π ch ch' hg ha]
  have hw : w1 π ch = w1 π ch' := by
    unfold w1
    rw [ha, weights_prefix π ch ch' hs hc hk]
  rw [hw]

/-- The final word needs neither kappa, the circle answers, nor queries. -/
theorem final_prefix (π : Fin 1024 ≃ Fin 1024) (ch ch' : Challenges K)
    (t : Trace K) (i : Fin 64)
    (hg : ch.opening 0 = ch'.opening 0) (ha : ch.opening 2 = ch'.opening 2)
    (hb : ch.opening 3 = ch'.opening 3) :
    BatchedLayer.read π ch t (.final i : R1Bat) =
      BatchedLayer.read π ch' t (.final i : R1Bat) := by
  rw [read_final, read_final, q1_local π ch ch' hg ha, hb]

#print axioms roundPoint_prefix
#print axioms zc_prefix
#print axioms semanticCoeff_prefix
#print axioms roundPoly_prefix
#print axioms batch_prefix
#print axioms weights_prefix
#print axioms round0_prefix
#print axioms round1_prefix
#print axioms final_prefix
end R1Z.PhaseMessageDependenciesBin
