import GSConcreteRootRecovery
import FixedInputBankUnionBound

set_option autoImplicit false
namespace AspisR1.GSFixedInputDecoderFamily
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
abbrev Lane (finalCount : Nat) := Fin 29 ⊕ Fin finalCount

structure Inputs (K : Type) (finalCount : Nat) where
  initialPoints : Fin 29 → Array (K × K)
  initialSize : ∀ i, (initialPoints i).size = 1048576
  finalPoints : Fin finalCount → Array (K × K)
  finalSize : ∀ i, (finalPoints i).size = 262144

abbrev Results (K : Type) (finalCount : Nat) :=
  (Fin 29 → Option (List (List K))) × (Fin finalCount → Option (List (List K)))

variable {finalCount : Nat} {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

/-- All input arrays are supplied before the tape. The initial calls share
one tape and the final calls share another; independence between calls is not
needed for completeness or the finite union bound. -/
def run (q t : Nat) (inputs : Inputs K finalCount) (H : InitialTape K t × FinalTape K t) :
    Results K finalCount :=
  (fun i => initial q t (inputs.initialPoints i) (inputs.initialSize i) H.1,
   fun i => final q t (inputs.finalPoints i) (inputs.finalSize i) H.2)

def failed (out : Results K finalCount) : Prop :=
  ∃ i : Lane finalCount, Sum.elim out.1 out.2 i = none

noncomputable section
variable [Fintype K]

theorem abort_le (q t : Nat) (inputs : Inputs K finalCount)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : InitialTape K t × FinalTape K t =>
      AspisV8R19.CausalFirstHitUnionBound.indicator (failed (run q t inputs H))) ≤
      29 * ((1025 : ℚ) * 112 * (1/2)^t) +
      (finalCount : ℚ) * ((256 : ℚ) * 112 * (1/2)^t) := by
  have h := AspisR1.FixedInputBankUnionBound.bank_union_le
    (fun (i : Fin 29) (H0 : InitialTape K t) =>
      initial q t (inputs.initialPoints i) (inputs.initialSize i) H0)
    (fun (i : Fin finalCount) (H1 : FinalTape K t) =>
      final q t (inputs.finalPoints i) (inputs.finalSize i) H1)
    ((1025 : ℚ) * 112 * (1/2)^t) ((256 : ℚ) * 112 * (1/2)^t)
    (fun i => initial_abort_le q t (inputs.initialPoints i) (inputs.initialSize i) hq hodd)
    (fun i => final_abort_le q t (inputs.finalPoints i) (inputs.finalSize i) hq hodd)
  simpa only [failed, run, Fintype.card_fin, Nat.cast_ofNat] using h

/-- The concrete second-fold caller can decode V and the four distinct
repeated channel words. Sharing the final tape does not change the union bound. -/
theorem abort_small_five (q : Nat) (inputs : Inputs K 5)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : InitialTape K 149 × FinalTape K 149 =>
      AspisV8R19.CausalFirstHitUnionBound.indicator (failed (run q 149 inputs H))) <
        (1/2 : ℚ)^127 := by
  apply lt_of_le_of_lt (abort_le q 149 inputs hq hodd)
  norm_num

#print axioms run
#print axioms abort_le
#print axioms abort_small_five
end
end AspisR1.GSFixedInputDecoderFamily
