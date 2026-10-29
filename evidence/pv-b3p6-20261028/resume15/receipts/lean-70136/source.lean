import PV_B3P_PatternBinding12227
import PV_B3P_Operations12227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding12227 Result ControlFlow
set_option autoImplicit false

abbrev PatternPowers15 := Array aspis_core.field.QM31 16#usize

def native_power_body15 (lambda : aspis_core.field.QM31)
    (state : PatternPowers15 × aspis_core.field.QM31 × Usize) :
    Result (ControlFlow (PatternPowers15 × aspis_core.field.QM31 × Usize) (PatternPowers15 × Usize)) :=
  if state.2.2 < 16#usize then do
    let powers ← Array.update state.1 state.2.2 state.2.1
    let power ← aspis_core.field.QM31.mul state.2.1 lambda
    .ok (.cont (powers,power,Usize.wrapping_add state.2.2 1#usize))
  else .ok (.done (state.1,state.2.2))

theorem native_power_body_binding15 (lambda : aspis_core.field.QM31)
    (powers : PatternPowers15) (power : aspis_core.field.QM31) (limb : Usize) :
    native_power_body15 lambda (powers,power,limb) =
      reference_copy_terminal.pattern_values_literal_loop0.body lambda powers power limb := by
  unfold native_power_body15 reference_copy_terminal.pattern_values_literal_loop0.body
  simp only [aspis_statement.poseidon2.POSEIDON2_WIDTH,lift,bind_tc_ok]

def native_pattern15 (openings : PatternPowers15) (lambda : aspis_core.field.QM31) : Result PatternResult12 := do
  let (powers,limb) ← loop (native_power_body15 lambda)
    (Array.repeat 16#usize aspis_core.field.QM31.ZERO,lambda,0#usize)
  source_pattern_outer12 openings powers limb (Array.repeat 14#usize aspis_core.field.QM31.ZERO) 0#usize

theorem native_pattern_binding15 (openings : PatternPowers15) (lambda : aspis_core.field.QM31) :
    native_pattern15 openings lambda = reference_copy_terminal.pattern_values_literal openings lambda := by
  rw [pattern_values_literal_binding12]
  unfold native_pattern15 source_pattern_values12 reference_copy_terminal.pattern_values_literal_loop0
  have bodies : native_power_body15 lambda =
      (fun state => reference_copy_terminal.pattern_values_literal_loop0.body lambda state.1 state.2.1 state.2.2) := by
    funext state
    exact native_power_body_binding15 lambda state.1 state.2.1 state.2.2
  rw [bodies]
#print axioms native_power_body_binding15
#print axioms native_pattern_binding15
end PV_B3P_Native15227
