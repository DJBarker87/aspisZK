import GSConcreteRootRecovery
import AspisV8R19.CausalFirstHitUnionBound

set_option autoImplicit false
namespace AspisR1.GSFixedInputDecoderBank
open CompPoly
open AspisR1.GSConcreteRootRecovery AspisR1.CompPolyFactorMeanTools
open AspisV8R19.OracleResampling
attribute [local irreducible] AspisR1.GSConcreteRootRecovery.initial
  AspisR1.GSConcreteRootRecovery.final
  AspisR1.GSConcreteInterpolation.initial AspisR1.GSConcreteInterpolation.final

abbrev InitialTape (K : Type) (t : Nat) :=
  {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → K × K
abbrev FinalTape (K : Type) (t : Nat) :=
  {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K
abbrev Lane := Fin 29 ⊕ Fin 2

structure Inputs (K : Type) where
  initialPoints : Fin 29 → Array (K × K)
  initialSize : ∀ i, (initialPoints i).size = 1048576
  finalPoints : Fin 2 → Array (K × K)
  finalSize : ∀ i, (finalPoints i).size = 262144

abbrev Results (K : Type) :=
  (Fin 29 → Option (List (List K))) × (Fin 2 → Option (List (List K)))

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

/-- All input arrays are supplied before the tape. The initial calls share
one tape and the final calls share another; independence between calls is not
needed for completeness or the finite union bound. -/
def run (q t : Nat) (inputs : Inputs K) (H : InitialTape K t × FinalTape K t) :
    Results K :=
  (fun i => initial q t (inputs.initialPoints i) (inputs.initialSize i) H.1,
   fun i => final q t (inputs.finalPoints i) (inputs.finalSize i) H.2)

def failed (out : Results K) : Prop :=
  ∃ i : Lane, Sum.elim out.1 out.2 i = none

noncomputable section
variable [Fintype K]

private theorem none_indicator_eq_abort {A : Type} (o : Option A) :
    AspisV8R19.CausalFirstHitUnionBound.indicator (o = none) = abortIndicator o := by
  cases o <;> simp [AspisV8R19.CausalFirstHitUnionBound.indicator, abortIndicator]

theorem abort_le (q t : Nat) (inputs : Inputs K)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : InitialTape K t × FinalTape K t =>
      AspisV8R19.CausalFirstHitUnionBound.indicator (failed (run q t inputs H))) ≤
      29 * ((1025 : ℚ) * 112 * (1/2)^t) +
      2 * ((256 : ℚ) * 112 * (1/2)^t) := by
  let bad : Lane → (InitialTape K t × FinalTape K t) → Prop := fun i H =>
    Sum.elim (run q t inputs H).1 (run q t inputs H).2 i = none
  let bound : Lane → ℚ := Sum.elim
    (fun _ => (1025 : ℚ) * 112 * (1/2)^t)
    (fun _ => (256 : ℚ) * 112 * (1/2)^t)
  have hb : ∀ i, mean (fun H =>
      AspisV8R19.CausalFirstHitUnionBound.indicator (bad i H)) ≤ bound i := by
    intro i
    cases i with
    | inl i =>
      change mean (fun H : InitialTape K t × FinalTape K t =>
        AspisV8R19.CausalFirstHitUnionBound.indicator
          (initial q t (inputs.initialPoints i) (inputs.initialSize i) H.1 = none)) ≤ _
      calc
        _ = mean (fun H0 : InitialTape K t => mean (fun _ : FinalTape K t =>
            AspisV8R19.CausalFirstHitUnionBound.indicator
              (initial q t (inputs.initialPoints i) (inputs.initialSize i) H0 = none))) :=
          mean_prod _
        _ = mean (fun H0 : InitialTape K t =>
            abortIndicator (initial q t (inputs.initialPoints i) (inputs.initialSize i) H0)) := by
          apply mean_congr
          intro H0
          rw [mean_const]
          exact none_indicator_eq_abort _
        _ ≤ _ := initial_abort_le q t (inputs.initialPoints i) (inputs.initialSize i) hq hodd
    | inr i =>
      change mean (fun H : InitialTape K t × FinalTape K t =>
        AspisV8R19.CausalFirstHitUnionBound.indicator
          (final q t (inputs.finalPoints i) (inputs.finalSize i) H.2 = none)) ≤ _
      calc
        _ = mean (fun _ : InitialTape K t => mean (fun H1 : FinalTape K t =>
            AspisV8R19.CausalFirstHitUnionBound.indicator
              (final q t (inputs.finalPoints i) (inputs.finalSize i) H1 = none))) :=
          mean_prod _
        _ = mean (fun H1 : FinalTape K t =>
            AspisV8R19.CausalFirstHitUnionBound.indicator
              (final q t (inputs.finalPoints i) (inputs.finalSize i) H1 = none)) := mean_const _
        _ = mean (fun H1 : FinalTape K t =>
            abortIndicator (final q t (inputs.finalPoints i) (inputs.finalSize i) H1)) :=
          mean_congr (fun H1 => none_indicator_eq_abort _)
        _ ≤ _ := final_abort_le q t (inputs.finalPoints i) (inputs.finalSize i) hq hodd
  have hu := AspisV8R19.CausalFirstHitUnionBound.mean_firstHit_union_le bad bound hb
  change mean (fun H : InitialTape K t × FinalTape K t =>
    AspisV8R19.CausalFirstHitUnionBound.indicator (∃ i : Lane, bad i H)) ≤ _
  have hsum : (∑ i : Lane, bound i) =
      29 * ((1025 : ℚ) * 112 * (1/2)^t) + 2 * ((256 : ℚ) * 112 * (1/2)^t) := by
    simp only [Lane, bound, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact hu.trans_eq hsum

theorem abort_small (q : Nat) (inputs : Inputs K)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : InitialTape K 149 × FinalTape K 149 =>
      AspisV8R19.CausalFirstHitUnionBound.indicator (failed (run q 149 inputs H))) <
        (1/2 : ℚ)^127 := by
  apply lt_of_le_of_lt (abort_le q 149 inputs hq hodd)
  norm_num

#print axioms run
#print axioms abort_le
#print axioms abort_small
end
end AspisR1.GSFixedInputDecoderBank
