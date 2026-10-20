import LiteralFreshBankStrictBound

set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralFreshTerminalFailurePathDomination

open AspisR1.LiteralFreshAbortComposition
open AspisR1.LiteralFreshBankAbortComposition
open AspisR1.LiteralFreshBankStrictBound
open AspisR1.LiteralFreshAttemptBound
open AspisR1.PerAttemptEnvelope
open AspisR1.LiteralTranscript
open AspisR1.GSConcreteByteDecoderBank
open AspisR1.GSFixedInputDecoderFamily
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.R572SequentialWordMass
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open FS FS2

attribute [local irreducible] LiteralByteSampler.samp LiteralClassifier.bad
attribute [local instance] Classical.propDecidable

variable {Aux : Type}

private theorem independent_mean_mono {I A O : Type} [Fintype A]
    (q : Program I A O) {f g : View I A O → ℚ} (h : ∀ v, f v ≤ g v) :
    independentMean q f ≤ independentMean q g := by
  induction q generalizing f g with
  | done o => exact h _
  | ask i next ih =>
    simp only [independentMean]
    exact FS.mean_mono fun a => ih a (fun v => h _)

/-- Average a terminal conditional failure mass over the fresh per-round
challenge programs. At depth zero, `terminalMass` is the remaining private-coin
failure probability for the completed log and auxiliary state. -/
def freshTerminalPathMean
    (choose : Prefix → Aux → LiteralTranscript.Message)
    (update : Prefix → LiteralTranscript.Message → Aux →
      View Bytes State LiteralTranscript.Challenge → Aux)
    (terminalMass : Prefix → Aux → ℚ) :
    Nat → Prefix → Aux → ℚ
  | 0, P, ctx => terminalMass P ctx
  | n + 1, P, ctx =>
    let m := choose P ctx
    independentMean (LiteralByteSampler.samp P.round P m).toProgram
      (fun v => freshTerminalPathMean choose update terminalMass n
        (P.ext m v.2) (update P m ctx v))

theorem freshTerminalPathMean_le_one
    (choose : Prefix → Aux → LiteralTranscript.Message)
    (update : Prefix → LiteralTranscript.Message → Aux →
      View Bytes State LiteralTranscript.Challenge → Aux)
    (terminalMass : Prefix → Aux → ℚ)
    (hterminal : ∀ P ctx, terminalMass P ctx ≤ 1)
    (n : Nat) (P : Prefix) (ctx : Aux) :
    freshTerminalPathMean choose update terminalMass n P ctx ≤ 1 := by
  induction n generalizing P ctx with
  | zero => exact hterminal P ctx
  | succ n ih =>
    change independentMean _ _ ≤ 1
    calc
      _ ≤ independentMean
          (LiteralByteSampler.samp P.round P (choose P ctx)).toProgram
          (fun _ => (1 : ℚ)) := by
            apply independent_mean_mono
            intro v
            exact ih (P.ext (choose P ctx) v.2) (update P (choose P ctx) ctx v)
      _ = 1 := independentMean_const _ _

/-- Fresh terminal path mass is bounded by `combinedMass` when its completed
log conditional failure mass is bounded by the supplied terminal envelope.
The recursion charges an earlier classifier hit at once; only a clean full
path reaches the terminal envelope. -/
theorem freshTerminalPathMean_le_combinedMass
    (choose : Prefix → Aux → LiteralTranscript.Message)
    (update : Prefix → LiteralTranscript.Message → Aux →
      View Bytes State LiteralTranscript.Challenge → Aux)
    (terminalMass abortMass : Prefix → Aux → ℚ)
    (hterminal : ∀ P ctx, P.rounds.length = 33 → terminalMass P ctx ≤ abortMass P ctx)
    (hbounded : ∀ P ctx, terminalMass P ctx ≤ 1)
    (n : Nat) (P : Prefix) (ctx : Aux)
    (hrows : P.rounds.length + n = 33) :
    freshTerminalPathMean choose update terminalMass n P ctx ≤
      combinedMass choose update abortMass n P ctx := by
  induction n generalizing P ctx with
  | zero =>
    simpa [freshTerminalPathMean, combinedMass] using
      hterminal P ctx (by omega)
  | succ n ih =>
    let m := choose P ctx
    change independentMean (LiteralByteSampler.samp P.round P m).toProgram
      (fun v => freshTerminalPathMean choose update terminalMass n
        (P.ext m v.2) (update P m ctx v)) ≤
      independentMean (LiteralByteSampler.samp P.round P m).toProgram
        (fun v => if LiteralClassifier.bad P m v.2 then 1 else
          combinedMass choose update abortMass n (P.ext m v.2)
            (update P m ctx v))
    apply independent_mean_mono
    intro v
    by_cases hb : LiteralClassifier.bad P m v.2
    · simp [hb]
      exact freshTerminalPathMean_le_one choose update terminalMass hbounded n
        (P.ext m v.2) (update P m ctx v)
    · simp [hb]
      apply ih
      simp only [FS.Prefix.ext, List.length_append, List.length_singleton]
      omega

/-- For the actual five-lane bank, any completed-log terminal failure mass
dominated by the no-hit bank-abort bound yields the existing adaptive fresh
challenge bound. `hterminal` is where the deterministic accepted-execution
event cover is instantiated; this theorem does not identify fresh-process
averaging with the shared-ROM experiment. -/
theorem fresh_terminal_failure_lt_100
    (choose : Prefix → Aux → LiteralTranscript.Message)
    (update : Prefix → LiteralTranscript.Message → Aux →
      View Bytes State LiteralTranscript.Challenge → Aux)
    (inputsAt : Prefix → Aux → Inputs K 5)
    (terminalMass : Prefix → Aux → ℚ)
    (pub : LiteralTranscript.Public) (ctx : Aux)
    (hterminal : ∀ P' ctx', P'.rounds.length = 33 →
      terminalMass P' ctx' ≤ bankAbortMass (inputsAt P' ctx'))
    (hbounded : ∀ P' ctx', terminalMass P' ctx' ≤ 1) :
    freshTerminalPathMean choose update terminalMass 33
      (FS.emptyPrefix pub) ctx < 1 / (2^100 : ℚ) := by
  calc
    _ ≤ combinedMass choose update
        (fun P c => bankAbortMass (inputsAt P c)) 33 (FS.emptyPrefix pub) ctx :=
          freshTerminalPathMean_le_combinedMass choose update terminalMass
            (fun P c => bankAbortMass (inputsAt P c)) hterminal hbounded 33
            (FS.emptyPrefix pub) ctx (by simp [FS.emptyPrefix])
    _ < 1 / (2^100 : ℚ) := actualBankCombinedMass_lt
      choose update inputsAt pub ctx

#print axioms freshTerminalPathMean
#print axioms freshTerminalPathMean_le_one
#print axioms freshTerminalPathMean_le_combinedMass
#print axioms fresh_terminal_failure_lt_100
end AspisR1.LiteralFreshTerminalFailurePathDomination
end
