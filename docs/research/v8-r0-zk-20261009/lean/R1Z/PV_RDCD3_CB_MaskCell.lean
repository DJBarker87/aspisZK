import R1Z.PV_RDCD3_CB_MaskIndices
import R1Z.PV_RDCD3_ArrayTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_MaskCell
open Aeneas Aeneas.Std Result PV_RDCD3_Total
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Coeff := Array Q 27#usize

def cell {N : Usize} (data : Array Q N) (exponents : Array U8 N)
    (column : Usize) (coefficients : Coeff) : Result Coeff := do
  let q ← Array.index_usize data column
  let coordinate ← lift (column &&& 3#usize)
  let q1 ← PV_RDCD3_CB_MaskSource.state_only_hiding.mul_tower_basis q coordinate
  let exponent ← Array.index_usize exponents column
  let slot ← lift (core.convert.num.FromUsizeU8.from exponent)
  Array.update coefficients slot q1

theorem total {N : Usize} (data : Array Q N) (exponents : Array U8 N)
    (column : Usize) (coefficients : Coeff) (inside : column.val<N.val)
    (exponent_safe : ∃ x,Array.index_usize exponents column=.ok x ∧ x.val<27) :
    Total (cell data exponents column coefficients) := by
  obtain ⟨q,hq⟩ := PV_RDCD3_ArrayRead.read data column inside
  obtain ⟨value,hvalue⟩ := PV_RDCD3_CB_MaskLeaves.tower q (column &&& 3#usize) (PV_RDCD3_CB_MaskIndices.coordinate column)
  obtain ⟨exponent,hexponent,bound⟩ := exponent_safe
  have slot_bound : (core.convert.num.FromUsizeU8.from exponent).val < (27#usize).val := by
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    exact bound
  obtain ⟨out,hout⟩ := PV_RDCD3_ArrayTotal.update_total coefficients _ value slot_bound
  refine ⟨out,?_⟩
  simp only [cell,hq,hvalue,hexponent,lift,bind_tc_ok,hout]
theorem c1_total (data : Array Q 16#usize) (column : Usize) (coefficients : Coeff)
    (inside : column.val<16) : Total (cell data PV_RDCD3_CB_MaskIndices.S.factors column coefficients) :=
  total data _ column coefficients inside (PV_RDCD3_CB_MaskIndices.factors_read column inside)
theorem mask_total (data : Array Q 10#usize) (column : Usize) (coefficients : Coeff)
    (inside : column.val<10) : Total (cell data PV_RDCD3_CB_MaskIndices.S.maskFactors column coefficients) :=
  total data _ column coefficients inside (PV_RDCD3_CB_MaskIndices.mask_factors_read column inside)
#print axioms total
#print axioms c1_total
#print axioms mask_total
end R1Z.PV_RDCD3_CB_MaskCell
