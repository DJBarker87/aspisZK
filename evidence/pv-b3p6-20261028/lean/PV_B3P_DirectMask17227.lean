import PV_B3P_MaskWhile14227
namespace PV_B3P_227
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
def host_copy_terminal.selector_mask_sum_16_loop.body
  (trailing_zeros : U16 → Result U32)
  (values : Array aspis_core.field.QM31 16#usize) (complement : Bool)
  (mask : Std.U16) (sum : aspis_core.field.QM31) :
  Result (ControlFlow (Std.U16 × aspis_core.field.QM31) aspis_core.field.QM31)
  := do
  if mask != 0#u16
  then
    let i ← trailing_zeros mask
    let index ← lift (UScalar.cast .Usize i)
    let sum1 ←
      if complement
      then
        do
        let q ← Array.index_usize values index
        aspis_core.field.QM31.sub sum q
      else
        do
        let q ← Array.index_usize values index
        aspis_core.field.QM31.add sum q
    let i1 ← lift (Std.U16.wrapping_sub mask 1#u16)
    let mask1 ← lift (mask &&& i1)
    ok (cont (mask1, sum1))
  else ok (done sum)

def host_copy_terminal.selector_mask_sum_16_loop
  (trailing_zeros : U16 → Result U32)
  (values : Array aspis_core.field.QM31 16#usize) (mask : Std.U16)
  (complement : Bool) (sum : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (mask1, sum1) => host_copy_terminal.selector_mask_sum_16_loop.body trailing_zeros
      values complement mask1 sum1)
    (mask, sum)

def host_copy_terminal.selector_mask_sum_16
  (count_ones trailing_zeros : U16 → Result U32)
  (values : Array aspis_core.field.QM31 16#usize) (mask : Std.U16) :
  Result aspis_core.field.QM31
  := do
  let i ← count_ones mask
  let (mask1, complement) ←
    if i > 8#u32
    then do
         let mask2 ← lift (~~~ mask)
         ok (mask2, true)
    else ok (mask, false)
  let sum ←
    if complement
    then ok aspis_core.field.QM31.ONE
    else ok aspis_core.field.QM31.ZERO
  host_copy_terminal.selector_mask_sum_16_loop trailing_zeros values mask1 complement sum
end PV_B3P_227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow
set_option autoImplicit false
attribute [local irreducible] Array.index_usize aspis_core.field.QM31.add aspis_core.field.QM31.sub

def mask_add17 (values : Array aspis_core.field.QM31 16#usize)
    (sum : aspis_core.field.QM31) (index : U32) : Result aspis_core.field.QM31 := do
  let q ← Array.index_usize values (UScalar.cast .Usize index)
  aspis_core.field.QM31.add sum q

theorem mask_loop_stop17 (zeros : U16 → Result U32)
    (values : Array aspis_core.field.QM31 16#usize) (sum : aspis_core.field.QM31) :
    host_copy_terminal.selector_mask_sum_16_loop zeros values 0#u16 false sum = .ok sum := by
  unfold host_copy_terminal.selector_mask_sum_16_loop
  rw [loop.eq_1]
  have zero : (0#u16 != 0#u16) = false := by rfl
  simp only [host_copy_terminal.selector_mask_sum_16_loop.body,zero,Bool.false_eq_true,if_false]

theorem mask_loop_step17 (zeros : U16 → Result U32)
    (values : Array aspis_core.field.QM31 16#usize) (mask : U16)
    (sum : aspis_core.field.QM31) (index : U32)
    (nonzero : mask ≠ 0#u16) (law : zeros mask = .ok index) :
    host_copy_terminal.selector_mask_sum_16_loop zeros values mask false sum = (do
      let next ← mask_add17 values sum index
      host_copy_terminal.selector_mask_sum_16_loop zeros values
        (mask &&& (U16.wrapping_sub mask 1#u16)) false next) := by
  unfold host_copy_terminal.selector_mask_sum_16_loop
  rw [loop.eq_1]
  have nonzero_bool : (mask != 0#u16) = true := by simp [nonzero]
  simp only [host_copy_terminal.selector_mask_sum_16_loop.body,nonzero_bool,if_true,
    law,lift,bind_tc_ok,Bool.false_eq_true,if_false,mask_add17,PV_B3P_Ordered227.bind_assoc]
  cases read : Array.index_usize values (UScalar.cast .Usize index) with
  | fail e => rfl
  | div => rfl
  | ok q =>
    simp only [bind_tc_ok]
    cases add : aspis_core.field.QM31.add sum q <;> rfl

#print axioms mask_loop_stop17
#print axioms mask_loop_step17
end PV_B3P_Direct17227
