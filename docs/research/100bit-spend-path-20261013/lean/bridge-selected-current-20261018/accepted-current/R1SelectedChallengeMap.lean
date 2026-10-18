import R1SelectedChallengeMapCore
import R1SelectedSamplerRanks

/-! Selected challenge maps for the 33-row mathematical transcript. Rows 25
and 26 carry the embedded QM31 parameter; their typed circle views apply the
existing row-specific total circle maps. Row 31's field value is unused by
the query sampler and is totalized to zero. This is not Rust refinement or
an instantiation of the complete message/decision/classifier protocol. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedChallengeMap
open AspisV8R19.SourceDuplexStep AspisWideTower AspisCircleGroupOrder
open R0P.SemSource


theorem gamma_row (s : State) :
    sigma 27 s = OpeningSamplerBound.gammaSample SelectedSamplerRanks.stateRank
      R0C.ModuloField.nonzeroRank s := by
  simp only [sigma, if_pos rfl]
  exact (SelectedSamplerRanks.gamma_eq s).symm

theorem opening_row (i : Nat) (hi : i = 28 ∨ i = 29 ∨ i = 30) (s : State) :
    sigma i s = OpeningSamplerBound.sample SelectedSamplerRanks.stateRank
      R0C.ModuloField.fieldRank s := by
  have h27 : i ≠ 27 := by omega
  simp only [sigma, if_neg h27, if_pos hi]
  exact (SelectedSamplerRanks.ordinary_eq s).symm

theorem semChal_re (s : State) : rhoOf (semChal s) = qm31Sample s := rfl

theorem circle_parameter_rows (s : State) :
    rhoOf (sigma 25 s) = qm31Sample s ∧
      rhoOf (sigma 26 s) = qm31Sample s := by
  simp [sigma, semChal_re]

theorem first_circle_view (s : State) :
    circleSampleParameter0 (rhoOf (sigma 25 s)) = circleSample0 s := by
  rw [(circle_parameter_rows s).1]
  rfl

theorem second_circle_view (s : State) :
    circleSampleParameter1 (rhoOf (sigma 26 s)) = circleSample1 s := by
  rw [(circle_parameter_rows s).2]
  rfl

theorem rho_row (s : State) :
    rhoOf (sigma 32 s) = qm31Rank
      (R0C.ModuloCounting.reduce (by norm_num [P]) (SelectedSamplerRanks.stateRank s)) := by
  simp only [sigma, show (32 : Nat) ≠ 27 by decide, if_false,
    show ¬ ((32 : Nat) = 28 ∨ 32 = 29 ∨ 32 = 30) by decide,
    show (32 : Nat) ≠ 31 by decide]
  rw [semChal_re]
  exact (SelectedSamplerRanks.qm31_eq s).symm

#print axioms semantic_row
#print axioms gamma_row
#print axioms opening_row
#print axioms semChal_re
#print axioms circle_parameter_rows
#print axioms first_circle_view
#print axioms second_circle_view
#print axioms rho_row
end AspisR1.SelectedChallengeMap
end
