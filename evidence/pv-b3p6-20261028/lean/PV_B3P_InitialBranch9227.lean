import PV_B3P_P227_09
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
attribute [local irreducible] host_terminal_field.PreparedQm31Multiplier.mul

theorem initial_low_branch9 (lane : Usize)
    (full_or_rate full : host_terminal_field.PreparedQm31Multiplier)
    (value : aspis_core.field.QM31) (h : lane < aspis_statement.poseidon2.RATE) :
    reference_terminal.initial_lane227 lane full_or_rate full value =
      host_terminal_field.PreparedQm31Multiplier.mul full_or_rate value := by
  simp only [reference_terminal.initial_lane227,h,↓reduceIte]

theorem initial_high_branch9 (lane : Usize)
    (full_or_rate full : host_terminal_field.PreparedQm31Multiplier)
    (value : aspis_core.field.QM31) (h : ¬lane < aspis_statement.poseidon2.RATE) :
    reference_terminal.initial_lane227 lane full_or_rate full value =
      host_terminal_field.PreparedQm31Multiplier.mul full value := by
  simp only [reference_terminal.initial_lane227,h,↓reduceIte]

#print axioms initial_low_branch9
#print axioms initial_high_branch9
end PV_B3P_Binding9227
