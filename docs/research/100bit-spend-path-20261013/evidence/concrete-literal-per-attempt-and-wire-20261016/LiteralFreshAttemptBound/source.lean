import LiteralBudgetEnvelope
import AspisV8R19.R572SequentialWordMass

/-! A single adaptive literal-transcript attempt with fresh answers inside
each row sampler. The classifier, concrete selected challenge maps and all33
literal row budgets are instantiated. Auxiliary context may carry arbitrary
history. This interpreter has no hidden retries and is distinct from the
shared-oracle experiment, whose bound retains its query factor. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralFreshAttemptBound
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.R572SequentialWordMass
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

attribute [local irreducible] LiteralByteSampler.samp LiteralClassifier.bad
variable {Aux : Type}

def hitMass
    (choose : LiteralTranscript.Prefix → Aux → LiteralTranscript.Message)
    (update : LiteralTranscript.Prefix → LiteralTranscript.Message → Aux →
      View Bytes State LiteralTranscript.Challenge → Aux) :
    Nat → LiteralTranscript.Prefix → Aux → ℚ
  | 0, _, _ => 0
  | n + 1, P, ctx =>
    let m := choose P ctx
    independentMean (LiteralByteSampler.samp P.round P m).toProgram
      (fun v => if LiteralClassifier.bad P m v.2 then 1 else
        hitMass choose update n (P.ext m v.2) (update P m ctx v))

theorem hitMass_le
    (choose : LiteralTranscript.Prefix → Aux → LiteralTranscript.Message)
    (update : LiteralTranscript.Prefix → LiteralTranscript.Message → Aux →
      View Bytes State LiteralTranscript.Challenge → Aux)
    (n : Nat) (P : LiteralTranscript.Prefix) (ctx : Aux)
    (hrows : P.rounds.length + n ≤ 33) :
    hitMass choose update n P ctx ≤ (n : ℚ) * PerAttemptEnvelope.B := by
  have hB : 0 ≤ PerAttemptEnvelope.B := by unfold PerAttemptEnvelope.B; positivity
  induction n generalizing P ctx with
  | zero => simp [hitMass]
  | succ n ih =>
    let m := choose P ctx
    have hrest : ∀ v : View Bytes State LiteralTranscript.Challenge,
        hitMass choose update n (P.ext m v.2) (update P m ctx v) ≤
          (n : ℚ) * PerAttemptEnvelope.B := by
      intro v
      apply ih
      simp only [FS.Prefix.ext,List.length_append,List.length_singleton]
      omega
    have hnB : 0 ≤ (n : ℚ) * PerAttemptEnvelope.B := mul_nonneg (Nat.cast_nonneg _) hB
    have hlen : P.round < 33 := by change P.rounds.length < 33; omega
    have hden := (LiteralClassifier.byte_density P m hlen).trans
      (LiteralBudgetEnvelope.row_le P.round hlen)
    change independentMean (LiteralByteSampler.samp P.round P m).toProgram
      (fun v => if LiteralClassifier.bad P m v.2 then 1 else
        hitMass choose update n (P.ext m v.2) (update P m ctx v)) ≤ _
    calc
      _ ≤ independentMean (LiteralByteSampler.samp P.round P m).toProgram
          (fun v => indicator (LiteralClassifier.bad P m v.2) +
            (n : ℚ) * PerAttemptEnvelope.B) := by
        apply independent_mono
        intro v
        by_cases hb : LiteralClassifier.bad P m v.2
        · simp only [indicator,if_pos hb]
          linarith
        · simp only [indicator,if_neg hb,zero_add]
          exact hrest v
      _ = independentMean (LiteralByteSampler.samp P.round P m).toProgram
          (fun v => indicator (LiteralClassifier.bad P m v.2)) +
          (n : ℚ) * PerAttemptEnvelope.B := by
        rw [independent_add,independentMean_const]
      _ ≤ PerAttemptEnvelope.B + (n : ℚ) * PerAttemptEnvelope.B := by linarith only [hden]
      _ = ((n + 1 : Nat) : ℚ) * PerAttemptEnvelope.B := by push_cast; ring

/-- Concrete per-attempt classifier failure mass is below 2^-100, without
subtracting grinding bits or dividing by work. It is not an unlimited-query
Fiat--Shamir probability statement or an acceptance-to-witness theorem. -/
theorem thirty_three_rows_lt
    (choose : LiteralTranscript.Prefix → Aux → LiteralTranscript.Message)
    (update : LiteralTranscript.Prefix → LiteralTranscript.Message → Aux →
      View Bytes State LiteralTranscript.Challenge → Aux)
    (pub : LiteralTranscript.Public) (ctx : Aux) :
    hitMass choose update 33 (FS.emptyPrefix pub) ctx < 1 / (2^100 : ℚ) := by
  exact (hitMass_le choose update 33 (FS.emptyPrefix pub) ctx (by simp [FS.emptyPrefix])).trans_lt
    PerAttemptEnvelope.thirty_three_B_lt

#print axioms hitMass_le
#print axioms thirty_three_rows_lt
end AspisR1.LiteralFreshAttemptBound
end
