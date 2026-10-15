import R1OpeningSamplerBound
import R1MatchingSupport
import R1UnifiedSamplerLaw

/-! Conditional density bounds for the four decoded opening rows.  The data
decoder is explicitly fixed by the prefix, message, and current table; this
file does not establish that decoder from a transcript or a source parser. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOpeningDensity

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open AspisCircleGroupOrder
open AspisR1.ConcreteBinding AspisR1.FunctionalWeights AspisR1.MatchingSupport
open TranscriptView Polynomial

variable {M : Type} {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E] {L : Nat}

abbrev DecodedOpening (E : Type) [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod P) E] :=
  {d : MatchingSupport.Data E // d.p0.natDegree ≤ 6 ∧ d.p1.natDegree ≤ 6}

def openingBad
    (decoded : UnifiedSampler.Prefix M E L → Message M → Table (Addr L) State →
      Option (DecodedOpening E))
    (P : UnifiedSampler.Prefix M E L) (m : Message M)
    (T : Table (Addr L) State) (ch : TranscriptView.Challenge E) : Prop :=
  match P.rounds.length, m, ch.1, decoded P m T with
  | 27, .payload _, .ordinary alpha, some ⟨d, _⟩ =>
      alpha ∈ ConcreteBinding.gammaBad d.W d.F d.Y
  | 28, .payload _, .ordinary alpha, some ⟨d, _⟩ =>
      alpha ∈ ConcreteBinding.kappaBad d.W d.F d.F0 d.Y d.c0 d.gamma
  | 29, .payload _, .ordinary alpha, some ⟨d, hdeg⟩ =>
      alpha ∈ ConcreteBinding.firstBad d.W d.gamma
        (FunctionalWeights.weights d.F d.F0 d.kappa) d.p0
  | 30, .payload _, .ordinary alpha, some ⟨d, hdeg⟩ =>
      alpha ∈ ConcreteBinding.secondBad d.W d.V d.gamma d.alpha0
        (FunctionalWeights.weights d.F d.F0 d.kappa) d.p1
  | _, _, _, _ => False

private theorem independentMean_zero {I A O : Type} [Fintype A] [Nonempty A]
    (q : Program I A O) :
    independentMean q (fun _ => (0 : ℚ)) = 0 := by
  induction q with
  | done _ => rfl
  | ask i k ih =>
      simp only [independentMean]
      rw [show (fun a => independentMean (k a) (fun _ => (0 : ℚ))) =
        fun _ => (0 : ℚ) from funext fun a => ih a]
      simp [mean_const]

private theorem openingCap_nonneg :
    0 ≤ OpeningSamplerBound.openingCap := by
  have hatom : 0 ≤ OpeningSamplerBound.atom := by
    unfold OpeningSamplerBound.atom
    positivity
  have hgamma : 0 ≤ OpeningSamplerBound.gammaAtom := by
    unfold OpeningSamplerBound.gammaAtom
    positivity
  unfold OpeningSamplerBound.openingCap
  nlinarith [mul_nonneg (by norm_num : (0 : ℚ) ≤ 336869026622539)
      hgamma,
    mul_nonneg (by norm_num : (0 : ℚ) ≤ 600 + 2 * 9396508281846)
      hatom]

private theorem gammaTerm_le_cap :
    (336869026622539 : ℚ) * OpeningSamplerBound.gammaAtom ≤
      OpeningSamplerBound.openingCap := by
  have hatom : 0 ≤ OpeningSamplerBound.atom := by
    unfold OpeningSamplerBound.atom
    positivity
  have hgamma : 0 ≤ OpeningSamplerBound.gammaAtom := by
    unfold OpeningSamplerBound.gammaAtom
    positivity
  unfold OpeningSamplerBound.openingCap
  exact le_add_of_nonneg_right
    (mul_nonneg (by norm_num : (0 : ℚ) ≤ 600 + 2 * 9396508281846) hatom)

private theorem kappaTerm_le_cap :
    (600 : ℚ) * OpeningSamplerBound.atom ≤ OpeningSamplerBound.openingCap := by
  have hatom : 0 ≤ OpeningSamplerBound.atom := by
    unfold OpeningSamplerBound.atom
    positivity
  have hgamma : 0 ≤ OpeningSamplerBound.gammaAtom := by
    unfold OpeningSamplerBound.gammaAtom
    positivity
  unfold OpeningSamplerBound.openingCap
  nlinarith [mul_nonneg (by norm_num : (0 : ℚ) ≤ 336869026622539)
      hgamma,
    mul_nonneg (by norm_num : (0 : ℚ) ≤ 2 * 9396508281846)
      hatom]

private theorem foldTerm_le_cap :
    (9396508281846 : ℚ) * OpeningSamplerBound.atom ≤
      OpeningSamplerBound.openingCap := by
  have hatom : 0 ≤ OpeningSamplerBound.atom := by
    unfold OpeningSamplerBound.atom
    positivity
  have hgamma : 0 ≤ OpeningSamplerBound.gammaAtom := by
    unfold OpeningSamplerBound.gammaAtom
    positivity
  unfold OpeningSamplerBound.openingCap
  nlinarith [mul_nonneg (by norm_num : (0 : ℚ) ≤ 336869026622539)
      hgamma,
    mul_nonneg (by norm_num : (0 : ℚ) ≤ 600 + 9396508281846)
      hatom]

theorem opening_density_bound (p : Params M E L) (hD : 5 ≤ p.D)
    (decoded : UnifiedSampler.Prefix M E L → Message M → Table (Addr L) State →
      Option (DecodedOpening E))
    (input : State ≃ Fin (2^256)) (output : Fin (P^8) ≃ E)
    (outputNZ : Fin (P^8 - 1) ≃ {x : E // x ≠ 0})
    (hσ27 : ∀ s : State,
      p.σ 27 s = OpeningSamplerBound.gammaSample input outputNZ s)
    (hσ28 : ∀ s : State,
      p.σ 28 s = OpeningSamplerBound.sample input output s)
    (hσ29 : ∀ s : State,
      p.σ 29 s = OpeningSamplerBound.sample input output s)
    (hσ30 : ∀ s : State,
      p.σ 30 s = OpeningSamplerBound.sample input output s) :
    ∀ (T : Table (Addr L) State) (i : Nat) (P : UnifiedSampler.Prefix M E L)
      (m : Message M), i < 33 → P.rounds.length = i →
      independentMean (UnifiedSampler.samp p hD i P m).toProgram
        (fun w => indicator (openingBad decoded P m T w.2)) ≤
          OpeningSamplerBound.openingCap := by
  intro T i P m hi hround
  have hcap := openingCap_nonneg
  by_cases hi27 : i = 27
  · subst i
    have hlen : P.rounds.length = 27 := by omega
    rw [hlen]
    cases m with
    | initial c1 =>
        have hzero : ∀ ch : TranscriptView.Challenge E,
            openingBad decoded P (.initial c1) T ch = False := by
          intro ch
          unfold openingBad
          rw [hlen]
          rfl
        have hz : (fun w : View (Addr L) State (TranscriptView.Challenge E) =>
            indicator (openingBad decoded P (.initial c1) T w.2)) =
            fun _ => (0 : ℚ) := by
          funext w
          rw [hzero w.2]
          exact indicator_false
        rw [hz, independentMean_zero]
        exact hcap
    | payload msg =>
        have hlaw := UnifiedSampler.unified_law p hD 27 P (.payload msg)
          (fun ch => indicator (openingBad decoded P (.payload msg) T ch))
          (by omega) (by simp [UnifiedSampler.messageValid])
        rw [hlaw]
        cases hd : decoded P (.payload msg) T with
        | none =>
            simp [openingBad, hlen, hd, mean_const, indicator_false]
            exact hcap
        | some data =>
            have hevent : ∀ b x,
                openingBad decoded P (.payload msg) T
                  (TranscriptView.liftChallenge (p.σ 27 b, x)) =
                    (p.σ 27 b ∈ ConcreteBinding.gammaBad data.val.W
                      data.val.F data.val.Y) := by
              intro b x
              simp [openingBad, hlen, hd, TranscriptView.liftChallenge]
            simp_rw [hevent, mean_const]
            have hmean :
                mean (fun b : State => indicator
                  (p.σ 27 b ∈ ConcreteBinding.gammaBad data.val.W
                    data.val.F data.val.Y)) =
                mean (fun a : State => indicator
                  (OpeningSamplerBound.gammaSample input outputNZ a ∈
                    ConcreteBinding.gammaBad data.val.W data.val.F data.val.Y)) := by
              apply mean_congr
              intro a
              rw [hσ27 a]
            rw [hmean]
            exact le_trans
              (OpeningSamplerBound.gamma_mass_le input outputNZ
                data.val.W data.val.F data.val.Y) gammaTerm_le_cap
  · by_cases hi28 : i = 28
    · subst i
      have hlen : P.rounds.length = 28 := by omega
      rw [hlen]
      cases m with
      | initial c1 =>
          have hzero : ∀ ch : TranscriptView.Challenge E,
              openingBad decoded P (.initial c1) T ch = False := by
            intro ch
            unfold openingBad
            rw [hlen]
            rfl
          have hz : (fun w : View (Addr L) State (TranscriptView.Challenge E) =>
              indicator (openingBad decoded P (.initial c1) T w.2)) =
              fun _ => (0 : ℚ) := by
            funext w
            rw [hzero w.2]
            exact indicator_false
          rw [hz, independentMean_zero]
          exact hcap
      | payload msg =>
          have hlaw := UnifiedSampler.unified_law p hD 28 P (.payload msg)
            (fun ch => indicator (openingBad decoded P (.payload msg) T ch))
            (by omega) (by simp [UnifiedSampler.messageValid])
          rw [hlaw]
          cases hd : decoded P (.payload msg) T with
          | none =>
              simp [openingBad, hlen, hd, mean_const, indicator_false]
              exact hcap
          | some data =>
              have hevent : ∀ b x,
                  openingBad decoded P (.payload msg) T
                    (TranscriptView.liftChallenge (p.σ 28 b, x)) =
                      (p.σ 28 b ∈ ConcreteBinding.kappaBad data.val.W
                        data.val.F data.val.F0 data.val.Y data.val.c0 data.val.gamma) := by
                intro b x
                simp [openingBad, hlen, hd, TranscriptView.liftChallenge]
              simp_rw [hevent, mean_const]
              have hmean :
                  mean (fun b : State => indicator
                    (p.σ 28 b ∈ ConcreteBinding.kappaBad data.val.W data.val.F
                      data.val.F0 data.val.Y data.val.c0 data.val.gamma)) =
                  mean (fun a : State => indicator
                    (OpeningSamplerBound.sample input output a ∈
                      ConcreteBinding.kappaBad data.val.W data.val.F data.val.F0
                        data.val.Y data.val.c0 data.val.gamma)) := by
                apply mean_congr
                intro a
                rw [hσ28 a]
              rw [hmean]
              exact le_trans
                (OpeningSamplerBound.kappa_mass_le input output data.val.W data.val.F
                  data.val.F0 data.val.Y data.val.c0 data.val.gamma) kappaTerm_le_cap
    · by_cases hi29 : i = 29
      · subst i
        have hlen : P.rounds.length = 29 := by omega
        rw [hlen]
        cases m with
        | initial c1 =>
            have hzero : ∀ ch : TranscriptView.Challenge E,
                openingBad decoded P (.initial c1) T ch = False := by
              intro ch
              unfold openingBad
              rw [hlen]
              rfl
            have hz : (fun w : View (Addr L) State (TranscriptView.Challenge E) =>
                indicator (openingBad decoded P (.initial c1) T w.2)) =
                fun _ => (0 : ℚ) := by
              funext w
              rw [hzero w.2]
              exact indicator_false
            rw [hz, independentMean_zero]
            exact hcap
        | payload msg =>
            have hlaw := UnifiedSampler.unified_law p hD 29 P (.payload msg)
              (fun ch => indicator (openingBad decoded P (.payload msg) T ch))
              (by omega) (by simp [UnifiedSampler.messageValid])
            rw [hlaw]
            cases hd : decoded P (.payload msg) T with
            | none =>
                simp [openingBad, hlen, hd, mean_const, indicator_false]
                exact hcap
            | some data =>
                have hevent : ∀ b x,
                    openingBad decoded P (.payload msg) T
                      (TranscriptView.liftChallenge (p.σ 29 b, x)) =
                        (p.σ 29 b ∈ ConcreteBinding.firstBad data.val.W data.val.gamma
                          (FunctionalWeights.weights data.val.F data.val.F0 data.val.kappa)
                          data.val.p0) := by
                  intro b x
                  simp [openingBad, hlen, hd, TranscriptView.liftChallenge]
                simp_rw [hevent, mean_const]
                have hmean :
                    mean (fun b : State => indicator
                      (p.σ 29 b ∈ ConcreteBinding.firstBad data.val.W data.val.gamma
                        (FunctionalWeights.weights data.val.F data.val.F0 data.val.kappa)
                        data.val.p0)) =
                    mean (fun a : State => indicator
                      (OpeningSamplerBound.sample input output a ∈
                        ConcreteBinding.firstBad data.val.W data.val.gamma
                          (FunctionalWeights.weights data.val.F data.val.F0 data.val.kappa)
                          data.val.p0)) := by
                  apply mean_congr
                  intro a
                  rw [hσ29 a]
                rw [hmean]
                exact le_trans
                  (OpeningSamplerBound.first_mass_le input output data.val.W data.val.gamma
                    (FunctionalWeights.weights data.val.F data.val.F0 data.val.kappa)
                    data.val.p0 data.property.1)
                  foldTerm_le_cap
      · by_cases hi30 : i = 30
        · subst i
          have hlen : P.rounds.length = 30 := by omega
          rw [hlen]
          cases m with
          | initial c1 =>
              have hzero : ∀ ch : TranscriptView.Challenge E,
                  openingBad decoded P (.initial c1) T ch = False := by
                intro ch
                unfold openingBad
                rw [hlen]
                rfl
              have hz : (fun w : View (Addr L) State (TranscriptView.Challenge E) =>
                  indicator (openingBad decoded P (.initial c1) T w.2)) =
                  fun _ => (0 : ℚ) := by
                funext w
                rw [hzero w.2]
                exact indicator_false
              rw [hz, independentMean_zero]
              exact hcap
          | payload msg =>
              have hlaw := UnifiedSampler.unified_law p hD 30 P (.payload msg)
                (fun ch => indicator (openingBad decoded P (.payload msg) T ch))
                (by omega) (by simp [UnifiedSampler.messageValid])
              rw [hlaw]
              cases hd : decoded P (.payload msg) T with
              | none =>
                  simp [openingBad, hlen, hd, mean_const, indicator_false]
                  exact hcap
              | some data =>
                  have hevent : ∀ b x,
                      openingBad decoded P (.payload msg) T
                        (TranscriptView.liftChallenge (p.σ 30 b, x)) =
                          (p.σ 30 b ∈ ConcreteBinding.secondBad data.val.W data.val.V
                            data.val.gamma data.val.alpha0
                            (FunctionalWeights.weights data.val.F data.val.F0 data.val.kappa)
                            data.val.p1) := by
                    intro b x
                    simp [openingBad, hlen, hd, TranscriptView.liftChallenge]
                  simp_rw [hevent, mean_const]
                  have hmean :
                      mean (fun b : State => indicator
                        (p.σ 30 b ∈ ConcreteBinding.secondBad data.val.W data.val.V
                          data.val.gamma data.val.alpha0
                          (FunctionalWeights.weights data.val.F data.val.F0 data.val.kappa)
                          data.val.p1)) =
                      mean (fun a : State => indicator
                        (OpeningSamplerBound.sample input output a ∈
                          ConcreteBinding.secondBad data.val.W data.val.V data.val.gamma
                            data.val.alpha0
                            (FunctionalWeights.weights data.val.F data.val.F0 data.val.kappa)
                            data.val.p1)) := by
                    apply mean_congr
                    intro a
                    rw [hσ30 a]
                  rw [hmean]
                  exact le_trans
                    (OpeningSamplerBound.second_mass_le input output data.val.W data.val.V
                      data.val.gamma data.val.alpha0
                      (FunctionalWeights.weights data.val.F data.val.F0 data.val.kappa)
                      data.val.p1 data.property.2)
                    foldTerm_le_cap
        · have hnot : i ≠ 27 ∧ i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 30 := by omega
          have hzero : ∀ ch : TranscriptView.Challenge E,
              openingBad decoded P m T ch = False := by
            intro ch
            cases m <;> simp [openingBad, hround, hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2]
          have hz : (fun w : View (Addr L) State (TranscriptView.Challenge E) =>
              indicator (openingBad decoded P m T w.2)) = fun _ => (0 : ℚ) := by
            funext w
            rw [hzero w.2]
            exact indicator_false
          rw [hz, independentMean_zero]
          exact hcap

#print axioms opening_density_bound

end AspisR1.UnifiedOpeningDensity
end
