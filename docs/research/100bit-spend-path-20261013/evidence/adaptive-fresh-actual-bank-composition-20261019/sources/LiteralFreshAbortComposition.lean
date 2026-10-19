import LiteralFreshAttemptBound

set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralFreshAbortComposition
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.R572SequentialWordMass
open AspisR1.LiteralFreshAttemptBound
open AspisR1.PerAttemptEnvelope
attribute [local irreducible] LiteralByteSampler.samp LiteralClassifier.bad
attribute [local instance] Classical.propDecidable

variable {Aux : Type}

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

/-- The challenge process keeps running through the current row, but immediately
charges classifier hits as failure. Only a classifier-clean completed prefix
uses the conditional extractor-abort mass at the base case. `abortMass` may
depend on the entire transcript and auxiliary context. -/
def combinedMass
    (choose : LiteralTranscript.Prefix → Aux → LiteralTranscript.Message)
    (update : LiteralTranscript.Prefix → LiteralTranscript.Message → Aux →
      View Bytes State LiteralTranscript.Challenge → Aux)
    (abortMass : LiteralTranscript.Prefix → Aux → ℚ) :
    Nat → LiteralTranscript.Prefix → Aux → ℚ
  | 0, P, ctx => abortMass P ctx
  | n + 1, P, ctx =>
    let m := choose P ctx
    independentMean (LiteralByteSampler.samp P.round P m).toProgram
      (fun v => if LiteralClassifier.bad P m v.2 then 1 else
        combinedMass choose update abortMass n (P.ext m v.2) (update P m ctx v))

/-- Adaptive averaging bridge: classifier hits over the 33 fresh challenge
rounds contribute at most `n*B`; transcript-dependent independent extractor
abort contributes only its conditional terminal bound `δ`. The terminal
premise is intentionally separate: the concrete caller must derive it from
accepted⇒parsed/semantic Checks, word recovery, and the fixed-log byte-bank
guarantee. -/
theorem combinedMass_le
    (choose : LiteralTranscript.Prefix → Aux → LiteralTranscript.Message)
    (update : LiteralTranscript.Prefix → LiteralTranscript.Message → Aux →
      View Bytes State LiteralTranscript.Challenge → Aux)
    (abortMass : LiteralTranscript.Prefix → Aux → ℚ)
    (δ : ℚ) (hδ : 0 ≤ δ)
    (n : Nat) (P : LiteralTranscript.Prefix) (ctx : Aux)
    (hrows : P.rounds.length + n = 33)
    (hterminal : ∀ P' ctx', P'.rounds.length = 33 → abortMass P' ctx' ≤ δ) :
    combinedMass choose update abortMass n P ctx ≤ (n : ℚ) * B + δ := by
  have hB : 0 ≤ B := by unfold B; positivity
  induction n generalizing P ctx with
  | zero =>
    simpa [combinedMass] using hterminal P ctx (by omega)
  | succ n ih =>
    let m := choose P ctx
    have hrest : ∀ v : View Bytes State LiteralTranscript.Challenge,
        combinedMass choose update abortMass n (P.ext m v.2) (update P m ctx v) ≤
          (n : ℚ) * B + δ := by
      intro v
      apply ih
      · simp only [FS.Prefix.ext, List.length_append, List.length_singleton]
        omega
    have hlen : P.round < 33 := by change P.rounds.length < 33; omega
    have hden : independentMean (LiteralByteSampler.samp P.round P m).toProgram
        (fun v => indicator (LiteralClassifier.bad P m v.2)) ≤ B :=
      (LiteralClassifier.byte_density P m hlen).trans
        (LiteralBudgetEnvelope.row_le P.round hlen)
    change independentMean (LiteralByteSampler.samp P.round P m).toProgram
      (fun v => if LiteralClassifier.bad P m v.2 then 1 else
        combinedMass choose update abortMass n (P.ext m v.2) (update P m ctx v)) ≤ _
    calc
      _ ≤ independentMean (LiteralByteSampler.samp P.round P m).toProgram
          (fun v => indicator (LiteralClassifier.bad P m v.2) + ((n : ℚ) * B + δ)) := by
        apply independent_mono
        intro v
        by_cases hb : LiteralClassifier.bad P m v.2
        · simp [indicator, hb]
          positivity
        · simp [indicator, hb]
          exact hrest v
      _ = independentMean (LiteralByteSampler.samp P.round P m).toProgram
          (fun v => indicator (LiteralClassifier.bad P m v.2)) + ((n : ℚ) * B + δ) := by
        rw [independent_add, independentMean_const]
      _ ≤ B + ((n : ℚ) * B + δ) := by linarith only [hden]
      _ = ((n + 1 : Nat) : ℚ) * B + δ := by push_cast; ring

#print axioms combinedMass
#print axioms combinedMass_le
end AspisR1.LiteralFreshAbortComposition
end
