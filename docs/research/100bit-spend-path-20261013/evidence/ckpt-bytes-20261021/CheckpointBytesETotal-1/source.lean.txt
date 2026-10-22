import CheckpointBytesE

set_option autoImplicit false
namespace AspisR1.CheckpointBytesETotal
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted CheckpointBytesE

/-- Out-of-range rejection occurs at the limb read before remainder/shift. -/
theorem e_byte_failure (q : RawE) (i : Usize) (outside : 32 ≤ i.val) :
    e_byte q i = fail Error.arrayOutOfBounds := by
  obtain ⟨j,hj,hv⟩ := UScalar.div_spec (x:=i) (y:=4#usize) (by decide)
  have beyond : 8 ≤ j.val := by change j.val = i.val/4 at hv; omega
  simp only [e_byte,aspis_core.field.wide_exact.WideExact.to_limbs,bind_tc_ok]
  rw [hj]
  simp [Array.index_usize,Array.make,List.getElem?_eq_none,beyond]

/-- Exact all-input execution, with successful bytes only within the field. -/
theorem e_byte_all (q : RawE) (i : Usize) :
    e_byte q i = if h : i.val < 32 then
      ok ((rawBytes q)[i.val]'(by rw [rawBytes_length]; exact h))
    else fail Error.arrayOutOfBounds := by
  by_cases h : i.val < 32
  · rw [dif_pos h]
    have eq : Usize.ofNat i.val (by scalar_tac) = i := by
      apply UScalar.eq_of_val_eq; simp
    simpa only [eq] using e_byte_raw q ⟨i.val,h⟩
  · rw [dif_neg h]
    exact e_byte_failure q i (by omega)

#print axioms e_byte_failure
#print axioms e_byte_all
end AspisR1.CheckpointBytesETotal
