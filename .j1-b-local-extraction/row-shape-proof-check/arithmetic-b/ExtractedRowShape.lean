import AspisR1RowShape.Funs

/-!
Exact result of the source-extracted row_shape declaration, checked against the
pinned Lean 4.31 Aeneas output. This is not a parser, prefix, or Rust-refinement
claim. Checked arithmetic is discharged before the finite row cases.
-/
namespace AspisR1.ExtractedRowShape
open Aeneas Aeneas.Std Result

private theorem tryMk_val {ty : UScalarTy} (x : UScalar ty) :
    UScalar.tryMk ty x.val = ok x := by
  have hx : UScalar.check_bounds ty x.val = true := by
    simpa only [UScalar.check_bounds, decide_eq_true_eq] using x.hBounds
  simp only [UScalar.tryMk, UScalar.tryMkOpt, hx, _root_.dite_true, Result.ofOption]
  congr 1

private theorem checked_mul_eq {ty : UScalarTy} (a b c : UScalar ty)
    (h : a.val * b.val = c.val) : a * b = ok c := by
  change UScalar.tryMk ty (a.val * b.val) = ok c
  rw [h]
  exact tryMk_val c

private theorem checked_add_eq {ty : UScalarTy} (a b c : UScalar ty)
    (h : a.val + b.val = c.val) : a + b = ok c := by
  change UScalar.tryMk ty (a.val + b.val) = ok c
  rw [h]
  exact tryMk_val c

/-- Exact checked computations; no platform-width specialization is needed. -/
theorem claims_eq : AspisR1RowShape.r1_wire.CLAIMS = ok 87#usize := by
  unfold AspisR1RowShape.r1_wire.CLAIMS AspisR1RowShape.r1_wire.POINTS
    AspisR1RowShape.r1_wire.LANES
  exact checked_mul_eq _ _ _ rfl

theorem claims_plus_lanes_eq : 87#usize + 29#usize = ok 116#usize :=
  checked_add_eq _ _ _ rfl

theorem claims_payload_eq : 116#usize * 32#usize = ok 3712#usize :=
  checked_mul_eq _ _ _ rfl

theorem lanes_payload_eq : 29#usize * 32#usize = ok 928#usize :=
  checked_mul_eq _ _ _ rfl

theorem sumcheck_payload_eq : 28#usize * 32#usize = ok 896#usize :=
  checked_mul_eq _ _ _ rfl

/-- The complete typed tag/payload-size table, including invalid U8 rows. -/
def table (row : U8) : Option (U8 × Usize) :=
  if row.val = 2 then some (1#u8, 32#usize)
  else if row.val = 14 then some (3#u8, 32#usize)
  else if row.val = 25 then some (4#u8, 3712#usize)
  else if row.val = 26 then some (5#u8, 928#usize)
  else if row.val ≤ 13 then some (0#u8, 0#usize)
  else if 15 ≤ row.val ∧ row.val ≤ 24 then some (2#u8, 896#usize)
  else none

end AspisR1.ExtractedRowShape

#print axioms AspisR1.ExtractedRowShape.claims_eq
#print axioms AspisR1.ExtractedRowShape.claims_plus_lanes_eq
#print axioms AspisR1.ExtractedRowShape.claims_payload_eq
#print axioms AspisR1.ExtractedRowShape.lanes_payload_eq
#print axioms AspisR1.ExtractedRowShape.sumcheck_payload_eq
