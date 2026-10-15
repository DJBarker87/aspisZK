import R1LiteralSemanticDensity
import R1LiteralCircleEvents
import R1LiteralOpeningDensity
import R1LiteralQueryDensity
import R1LiteralRhoDensity
import R1ConcretePackBasis
import R1LiteralByteSampler

/-! A row-indexed union of the already checked independent-answer events for
the literal transcript sampler. This is a density dispatch only; it does not
prove an accepted-execution terminal implication or source correspondence. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralClassifier

open FS FS2
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw
attribute [local instance] Classical.propDecidable

open AspisR1.LiteralTranscript

def bad (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (c : LiteralTranscript.Challenge) : Prop :=
  if P.round < 25 then
    LiteralSemanticDensity.event ConcretePackBasis.basis P m c
  else
    match P.round with
    | 25 => LiteralOrdinaryDensity.event P m LiteralCircleDensity.bad0 c
    | 26 => LiteralOrdinaryDensity.event P m (LiteralCircleEvents.bad1 P) c
    | 27 => LiteralOrdinaryDensity.event P m (LiteralOpeningEvents.gammaBad P m) c
    | 28 => LiteralOrdinaryDensity.event P m (LiteralOpeningEvents.kappaBad P m) c
    | 29 => LiteralOrdinaryDensity.event P m (LiteralOpeningEvents.firstBad P m) c
    | 30 => LiteralOrdinaryDensity.event P m (LiteralOpeningEvents.secondBad P m) c
    | 31 => LiteralQueryDensity.bad P m c
    | 32 => LiteralOrdinaryDensity.event P m (LiteralRhoDensity.bad P) c
    | _ => False

def budget (i : Nat) : ℚ :=
  if i < 25 then R0P.SemSource.combinedD2BudgetZ i
  else
    match i with
    | 25 | 26 => LiteralCircleDensity.budget
    | 27 => LiteralOpeningDensity.gammaBudget
    | 28 => LiteralOpeningDensity.kappaBudget
    | 29 | 30 => LiteralOpeningDensity.foldBudget
    | 31 => UnifiedQueryDensity.queryCap
    | 32 => RhoSamplerBound.rhoCap
    | _ => 0

theorem density (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hi : P.round < 33) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (bad P m v.2)) ≤ budget P.round := by
  by_cases h25 : P.round < 25
  · simpa [bad, budget, h25] using
      LiteralSemanticDensity.density ConcretePackBasis.basis P m h25
  · have hrow : P.round = 25 ∨ P.round = 26 ∨ P.round = 27 ∨
        P.round = 28 ∨ P.round = 29 ∨ P.round = 30 ∨
        P.round = 31 ∨ P.round = 32 := by omega
    rcases hrow with h | h | h | h | h | h | h | h
    · simpa [bad, budget, h25, h] using LiteralCircleDensity.row25_density P m h
    · simpa [bad, budget, h25, h] using LiteralCircleEvents.row26_density P m h
    · simpa [bad, budget, h25, h] using LiteralOpeningDensity.row27_density P m h
    · simpa [bad, budget, h25, h] using LiteralOpeningDensity.row28_density P m h
    · simpa [bad, budget, h25, h] using LiteralOpeningDensity.row29_density P m h
    · simpa [bad, budget, h25, h] using LiteralOpeningDensity.row30_density P m h
    · simpa [bad, budget, h25, h] using LiteralQueryDensity.row31_density P m h
    · simpa [bad, budget, h25, h] using LiteralRhoDensity.row32_density P m h

theorem byte_density (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hi : P.round < 33) :
    independentMean (LiteralByteSampler.samp P.round P m).toProgram
      (fun v => indicator (bad P m v.2)) ≤ budget P.round := by
  rw [LiteralByteSampler.independentMean_eq]
  exact density P m hi

#print axioms density
#print axioms byte_density

end AspisR1.LiteralClassifier
end
