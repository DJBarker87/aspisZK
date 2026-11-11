import AspisPairResidualBridge
import R1LiteralRhoDensity

/-! Row 32 (the batching challenge) of the Aspis one-transaction transcript:
the bad event for the residual pair, read from the completed prefix, and its
independent-answer density.

Kind of result: MODEL THEOREMS in R1's literal-transcript classifier model.
The event reads the matching data and the ordered queries from the literal
prefix through R1's own reader `LiteralRhoDensity.read` (completed rows
through 31: the C1 word in row 0, the C2 word in row 2, the folded word in
row 30, the final message in row 31, challenges through 30, queries at 31),
so it is fixed before the row-32 answer. The density is R1's cap `rhoCap`
(the pair set has at most 21 elements, like R1's). This is an
independent-answer density, not acceptance, binding or a source statement;
the 40-row Aspis protocol instance, decoder and classifier that would consume
it do not exist yet. -/

set_option autoImplicit false
noncomputable section
namespace AspisPairResidual.Row32

open FS FS2
open AspisCircleGroupOrder
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.SourceDuplexStep
open AspisR1
attribute [local instance] Classical.propDecidable

/-- The row-32 bad event for the Aspis residual pair. Same reader and same
challenge projection as R1's `LiteralRhoDensity.bad`; only the set differs. -/
def bad (P : LiteralTranscript.Prefix) (v : AspisWideTower.WideExact) : Prop :=
  match LiteralRhoDensity.read P with
  | none => False
  | some (d, q) => SelectedChallengeMap.rhoOf v ∈
      AspisPairResidual.pairBad LiteralOpeningView.eK d q

/-- Balanced modulo reduction against the pair set (R1's
`RhoSamplerBound.modulo_bad_mass` with `pairBad` in place of `rhoBad`). -/
theorem modulo_pair_bad_mass {A K E : Type} [Fintype A] [Field K] [Fintype K]
    [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod P) E]
    {B n : Nat} (hn : 0 < n)
    (input : A ≃ Fin B) (output : Fin n ≃ K)
    (iota : K →+* E) (d : MatchingSupport.Data E) (q : Fin 22 → Fin 262144) :
    mean (fun a : A => indicator
      (output (R0C.ModuloCounting.reduce hn (input a)) ∈
        AspisPairResidual.pairBad iota d q)) ≤
      21 * (((B / n + 1 : Nat) : ℚ) / B) := by
  have hmass := R0C.ModuloCounting.event_mass_le
    (fun a : A => output (R0C.ModuloCounting.reduce hn (input a)))
    (((B / n + 1 : Nat) : ℚ) / B)
    (R0C.ModuloCounting.encoded_mass_le hn input output)
    (AspisPairResidual.pairBad iota d q)
  apply hmass.trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast AspisPairResidual.pairBad_card iota d q
  · positivity

theorem pair_mean (P : LiteralTranscript.Prefix) :
    mean (fun s : State => indicator (bad P (SelectedChallengeMap.sigma 32 s))) ≤
      RhoSamplerBound.rhoCap := by
  cases h : LiteralRhoDensity.read P with
  | none =>
      simp only [bad, h, indicator_false, mean_const]
      exact LiteralRhoDensity.budget_nonneg
  | some dq =>
      rcases dq with ⟨d, q⟩
      simp only [bad, h, SelectedChallengeMap.rho_row]
      exact modulo_pair_bad_mass
        (by norm_num [AspisCircleGroupOrder.P]) SelectedSamplerRanks.stateRank
        R0P.SemSource.qm31Rank LiteralOpeningView.eK d q

/-- The row-32 density for the pair, at R1's cap. -/
theorem row32_pair_density (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hround : P.round = 32) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (LiteralOrdinaryDensity.event P m (bad P) v.2)) ≤
      RhoSamplerBound.rhoCap := by
  apply LiteralOrdinaryDensity.density P m (bad P) RhoSamplerBound.rhoCap
  · omega
  · exact LiteralRhoDensity.budget_nonneg
  · simpa only [hround] using pair_mean P

/-- R1 recovered: on a prefix whose data satisfy every per-query first-fold
equality, the pair event is R1's row-32 event. -/
theorem bad_iff_r1_of_match0 (P : LiteralTranscript.Prefix) (v : AspisWideTower.WideExact)
    (d : MatchingSupport.Data AspisWideTower.WideExact) (q : Fin 22 → Fin 262144)
    (hread : LiteralRhoDensity.read P = some (d, q))
    (hfirst : ∀ i, MatchingSupport.match0 d (q i)) :
    bad P v ↔ LiteralRhoDensity.bad P v := by
  simp only [bad, LiteralRhoDensity.bad, hread]
  rw [AspisPairResidual.pairBad_eq_rhoBad_of_match0 LiteralOpeningView.eK d q hfirst]

#print axioms modulo_pair_bad_mass
#print axioms pair_mean
#print axioms row32_pair_density
#print axioms bad_iff_r1_of_match0

end AspisPairResidual.Row32
end
