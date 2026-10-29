import PV_B3P_ArrayWrite227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false
abbrev Matrix3x3 := Array (Array U64 3#usize) 3#usize

def matrix_cell (sums : Matrix3x3) (component channel : Usize)
    (left right : U32) : Result Matrix3x3 := do
  let l ← lift (UScalar.cast .U64 left)
  let r ← lift (UScalar.cast .U64 right)
  let product ← lift (U64.wrapping_mul l r)
  let old_row ← Array.index_usize sums component
  let old ← Array.index_usize old_row channel
  let next ← lift (U64.wrapping_add old product)
  let (row,back) ← Array.index_mut_usize sums component
  let updated ← Array.update row channel next
  .ok (back updated)

def matrix_put (sums : Matrix3x3) (component channel : Usize)
    (hc : component.val<3) (hk : channel.val<3) (left right : U32) : Matrix3x3 :=
  let row := sums.val[component.val]'(by simpa only [sums.property] using hc)
  let old := row.val[channel.val]'(by simpa only [row.property] using hk)
  let product := U64.wrapping_mul (UScalar.cast .U64 left) (UScalar.cast .U64 right)
  Array.set sums component (Array.set row channel (U64.wrapping_add old product))

attribute [local irreducible] U64.wrapping_mul U64.wrapping_add

theorem matrix_cell_result (sums : Matrix3x3) (component channel : Usize)
    (hc : component.val<3) (hk : channel.val<3) (left right : U32) :
    matrix_cell sums component channel left right =
      .ok (matrix_put sums component channel hc hk left right) := by
  have hc' : component.val<(3#usize).val := hc
  let row := sums.val[component.val]'(by simpa only [sums.property] using hc)
  have hk' : channel.val<(3#usize).val := hk
  unfold matrix_cell
  simp only [lift,bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value sums component hc']
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value _ channel hk']
  simp only [bind_tc_ok]
  rw [PV_B3P_ArrayWrite227.borrow sums component hc']
  simp only [bind_tc_ok]
  rw [PV_B3P_ArrayWrite227.update _ channel hk']
  rfl

#print axioms matrix_cell_result
end PV_B3P_Binding9227
