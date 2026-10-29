import PV_B3P_P227_13a
import PV_B3P_Success227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
theorem read_helper_binding8 {N : Usize} (values : Array aspis_core.field.QM31 N) (i : Usize) :
    reference_terminal.read227 values i = Array.index_usize values i := rfl

theorem digest_helper_binding8 (values : Array (Array U32 8#usize) 20#usize) (i : Usize) :
    reference_terminal.digest227 values i = Array.index_usize values i := rfl

/-- The original direct read body, with identical decrement/multiply/read/add order. -/
def horner_direct_body8 {N : Usize} (values : Array aspis_core.field.QM31 N)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize) :
    Result (ControlFlow (aspis_core.field.QM31 × Usize) aspis_core.field.QM31) := do
  if index > 0#usize then
    let next ← lift (Usize.wrapping_sub index 1#usize)
    let product ← host_terminal_field.PreparedQm31Multiplier.mul prepared composition
    let value ← Array.index_usize values next
    let sum ← aspis_core.field.QM31.add product value
    Result.ok (.cont (sum,next))
  else Result.ok (.done composition)

attribute [local irreducible] host_terminal_field.PreparedQm31Multiplier.mul
  aspis_core.field.QM31.add Array.index_usize

theorem horner_semantic_body_binding8 (values : Array aspis_core.field.QM31 24#usize)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize) :
    reference_terminal.composition_parts_loop1.body values prepared composition index =
      horner_direct_body8 values prepared composition index := by
  unfold reference_terminal.composition_parts_loop1.body horner_direct_body8
  simp only [read_helper_binding8]
#print axioms horner_semantic_body_binding8

theorem horner_poseidon_body_binding8 (values : Array aspis_core.field.QM31 4#usize)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize) :
    reference_terminal.composition_parts_loop2.body values prepared composition index =
      horner_direct_body8 values prepared composition index := by
  unfold reference_terminal.composition_parts_loop2.body horner_direct_body8
  simp only [read_helper_binding8]
#print axioms horner_poseidon_body_binding8

#print axioms read_helper_binding8
#print axioms digest_helper_binding8
end PV_B3P_Success227
