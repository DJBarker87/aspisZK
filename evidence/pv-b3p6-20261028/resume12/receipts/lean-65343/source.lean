import PV_B3P_E227_15
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

def source_pattern_step12
    (pattern : reference_copy_terminal.CompiledPoolV1PairForestPattern)
    (limb : Usize) (openings powers : Array aspis_core.field.QM31 16#usize)
    (value : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let kind ← Array.index_usize pattern.kinds limb
  if kind = 1#u8 then
    let column ← Array.index_usize pattern.columns limb
    let index ← lift (core.convert.num.FromUsizeU8.from column)
    let opened ← Array.index_usize openings index
    let offset ← Array.index_usize pattern.offsets limb
    let lifted ← reference_copy_terminal.lift_m31 offset
    let source ← aspis_core.field.QM31.add opened lifted
    let power ← Array.index_usize powers limb
    let weighted ← aspis_core.field.QM31.mul power source
    aspis_core.field.QM31.add value weighted
  else .ok value

attribute [local irreducible] Array.index_usize reference_copy_terminal.lift_m31
  aspis_core.field.QM31.add aspis_core.field.QM31.mul

theorem pattern_step_binding12
    (pattern : reference_copy_terminal.CompiledPoolV1PairForestPattern)
    (limb : Usize) (openings powers : Array aspis_core.field.QM31 16#usize)
    (value : aspis_core.field.QM31) :
    reference_copy_terminal.pattern_limb227 pattern limb openings powers value =
      source_pattern_step12 pattern limb openings powers value := by
  unfold reference_copy_terminal.pattern_limb227 source_pattern_step12
  apply PV_B3P_Binding9227.bind_equal9
  intro kind
  rfl

#print axioms pattern_step_binding12
end PV_B3P_Binding12227
