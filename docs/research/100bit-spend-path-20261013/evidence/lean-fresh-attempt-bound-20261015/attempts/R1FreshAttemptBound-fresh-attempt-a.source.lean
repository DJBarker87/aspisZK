import R1UnifiedSampler
import R1PerAttemptEnvelope
import AspisV8R19.R572SequentialWordMass

/-! Adaptive fresh-answer transcript attempts. This interpreter draws fresh
answers inside each row sampler; it is not the memoized random-oracle
experiment and allows no hidden challenge retries between the modeled rows.
The event and context update remain explicit parameters. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.FreshAttemptBound

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.R572SequentialWordMass
open TranscriptView

attribute [local instance] Classical.propDecidable

private theorem independent_mono {I A O : Type} [Fintype A]
    (q : Program I A O) {f g : View I A O → ℚ} (h : ∀ v, f v ≤ g v) :
    independentMean q f ≤ independentMean q g := by
  induction q generalizing f g with
  | done o => exact h _
  | ask i next ih =>
    simp only [independentMean]
    exact FS.mean_mono fun a => ih a (fun v => h _)

private theorem independent_add {I A O : Type} [Fintype A]
    (q : Program I A O) (f g : View I A O → ℚ) :
    independentMean q (fun v => f v + g v) =
      independentMean q f + independentMean q g := by
  induction q generalizing f g with
  | done o => rfl
  | ask i next ih =>
    simp only [independentMean]
    rw [mean_congr (fun a => ih a _ _), FS.mean_add]

variable {M Cv : Type} {L : Nat}

def hitMass (p : Params M Cv L) (hD : 5 ≤ p.D)
    (bad : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      Challenge Cv → Prop)
    (choose : UnifiedSampler.Prefix M Cv L → Table (Addr L) State → Message M)
    (update : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      View (Addr L) State (Challenge Cv) → Table (Addr L) State) :
    Nat → UnifiedSampler.Prefix M Cv L → Table (Addr L) State → ℚ
  | 0, _, _ => 0
  | n + 1, P, T =>
    let m := choose P T
    independentMean (UnifiedSampler.samp p hD P.rounds.length P m).toProgram
      (fun v => if bad P m T v.2 then 1 else
        hitMass p hD bad choose update n (P.ext m v.2) (update P m T v))

/-- A union bound for an adaptive sequence with fresh sampler answers.
The table-shaped auxiliary context may be updated arbitrarily after each row.
Nothing here identifies it with a shared-oracle execution. -/
theorem hitMass_le (p : Params M Cv L) (hD : 5 ≤ p.D)
    (bad : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      Challenge Cv → Prop)
    (choose : UnifiedSampler.Prefix M Cv L → Table (Addr L) State → Message M)
    (update : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      View (Addr L) State (Challenge Cv) → Table (Addr L) State)
    (B : ℚ) (hB : 0 ≤ B)
    (hdensity : ∀ P m T, P.rounds.length < 33 →
      independentMean (UnifiedSampler.samp p hD P.rounds.length P m).toProgram
        (fun v => indicator (bad P m T v.2)) ≤ B)
    (n : Nat) (P : UnifiedSampler.Prefix M Cv L) (T : Table (Addr L) State)
    (hrows : P.rounds.length + n ≤ 33) :
    hitMass p hD bad choose update n P T ≤ (n : ℚ) * B := by
  induction n generalizing P T with
  | zero => simp [hitMass]
  | succ n ih =>
    let m := choose P T
    have hrest : ∀ v : View (Addr L) State (Challenge Cv),
        hitMass p hD bad choose update n (P.ext m v.2) (update P m T v) ≤
          (n : ℚ) * B := by
      intro v
      apply ih
      simp only [FS.Prefix.ext, List.length_append, List.length_singleton]
      omega
    have hnB : 0 ≤ (n : ℚ) * B := mul_nonneg (Nat.cast_nonneg _) hB
    change independentMean (UnifiedSampler.samp p hD P.rounds.length P m).toProgram
      (fun v => if bad P m T v.2 then 1 else
        hitMass p hD bad choose update n (P.ext m v.2) (update P m T v)) ≤ _
    calc
      _ ≤ independentMean (UnifiedSampler.samp p hD P.rounds.length P m).toProgram
          (fun v => indicator (bad P m T v.2) + (n : ℚ) * B) := by
        apply independent_mono
        intro v
        by_cases hb : bad P m T v.2
        · simp only [if_pos hb, indicator, if_pos hb]
          linarith
        · simp only [if_neg hb, indicator, if_neg hb, zero_add]
          exact hrest v
      _ = independentMean (UnifiedSampler.samp p hD P.rounds.length P m).toProgram
          (fun v => indicator (bad P m T v.2)) + (n : ℚ) * B := by
        rw [independent_add, independentMean_const]
      _ ≤ B + (n : ℚ) * B := add_le_add_right (hdensity P m T (by omega)) _
      _ = ((n + 1 : Nat) : ℚ) * B := by push_cast; ring

theorem thirty_three_hitMass_lt (p : Params M Cv L) (hD : 5 ≤ p.D)
    (bad : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      Challenge Cv → Prop)
    (choose : UnifiedSampler.Prefix M Cv L → Table (Addr L) State → Message M)
    (update : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      View (Addr L) State (Challenge Cv) → Table (Addr L) State)
    (hdensity : ∀ P m T, P.rounds.length < 33 →
      independentMean (UnifiedSampler.samp p hD P.rounds.length P m).toProgram
        (fun v => indicator (bad P m T v.2)) ≤ PerAttemptEnvelope.B)
    (pub : UnifiedSampler.Public L) (T : Table (Addr L) State) :
    hitMass p hD bad choose update 33 (FS.emptyPrefix pub) T < 1 / (2^100 : ℚ) := by
  apply (hitMass_le p hD bad choose update PerAttemptEnvelope.B
    (by unfold PerAttemptEnvelope.B; positivity) hdensity 33 (FS.emptyPrefix pub) T
    (by simp [FS.emptyPrefix])).trans_lt
  exact PerAttemptEnvelope.thirty_three_B_lt

#print axioms hitMass_le
#print axioms thirty_three_hitMass_lt
end AspisR1.FreshAttemptBound
end
