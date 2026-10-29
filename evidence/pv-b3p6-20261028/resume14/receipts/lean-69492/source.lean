import PV_B3P_MaskWhile14_1749227
import PV_B3P_MaskWhile14_2048227
import PV_B3P_MaskWhile14_2049227
import PV_B3P_MaskWhile14_4097227
import PV_B3P_MaskWhile14_6144227
import PV_B3P_MaskWhile14_6145227
import PV_B3P_MaskWhile14_26214227
namespace PV_B3P_Correct14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Success227 Result ControlFlow
set_option autoImplicit false

def native_mask_body14 (values : Array aspis_core.field.QM31 16#usize) (complement : Bool)
    (state : Nat × aspis_core.field.QM31) :
    Result (ControlFlow (Nat × aspis_core.field.QM31) aspis_core.field.QM31) :=
  if state.1 = 0 then .ok (.done state.2)
  else do
    let value ← mask_read10 values (PV_B3P_Mask227.trailing 16 state.1)
    let next ← if complement then aspis_core.field.QM31.sub state.2 value else aspis_core.field.QM31.add state.2 value
    .ok (.cont (clear_mask14 state.1,next))

def native_mask14 (values : Array aspis_core.field.QM31 16#usize) (mask : U16) :
    Result aspis_core.field.QM31 :=
  let complement : Bool := decide (8 < PV_B3P_Mask227.popcount mask.val)
  let bits := if complement then 65535-mask.val else mask.val
  let initial := if complement then aspis_core.field.QM31.ONE else aspis_core.field.QM31.ZERO
  loop (native_mask_body14 values complement) (bits,initial)

theorem native_mask_add_body14 (values : Array aspis_core.field.QM31 16#usize) :
    native_mask_body14 values false = mask_while_body14 values := by
  funext state
  unfold native_mask_body14 mask_while_body14 mask_step10
  split
  · rfl
  · simp only [Bool.false_eq_true,if_false,PV_B3P_Ordered227.bind_assoc]

theorem native_mask_on_domain14 (values : Array aspis_core.field.QM31 16#usize)
    (mask : U16) (allowed : MaskAllowed mask) :
    native_mask14 values mask = source_mask11 values mask := by
  have off : ¬ 8 < PV_B3P_Mask227.popcount mask.val := Nat.not_lt.mpr (complement_off_on_domain14 mask allowed)
  unfold native_mask14
  simp only [off,decide_false,Bool.false_eq_true,if_false,native_mask_add_body14]
  change mask_while14 values mask.val aspis_core.field.QM31.ZERO = source_mask11 values mask
  rcases allowed with h|h|h|h|h|h|h
  · subst mask; exact mask_while_1749_14 values
  · subst mask; exact mask_while_2048_14 values
  · subst mask; exact mask_while_2049_14 values
  · subst mask; exact mask_while_4097_14 values
  · subst mask; exact mask_while_6144_14 values
  · subst mask; exact mask_while_6145_14 values
  · subst mask; exact mask_while_26214_14 values

theorem native_mask_link14 : PV_B3P_Link_mask_on_domain native_mask14 := by
  intro values mask allowed
  exact Eq.trans (native_mask_on_domain14 values mask allowed) (mask_direct14 values mask allowed)

theorem native_mask_zero14 (values : Array aspis_core.field.QM31 16#usize) :
    native_mask14 values 0#u16 = .ok aspis_core.field.QM31.ZERO := by
  unfold native_mask14
  change loop (native_mask_body14 values false) (0,aspis_core.field.QM31.ZERO) = _
  rw [loop.eq_1]
  rfl
#print axioms native_mask_add_body14
#print axioms native_mask_on_domain14
#print axioms native_mask_link14
#print axioms native_mask_zero14
end PV_B3P_Correct14227
