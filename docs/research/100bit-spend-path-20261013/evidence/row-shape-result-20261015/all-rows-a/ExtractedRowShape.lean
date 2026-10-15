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

/-- All out-of-range U8 values are rejected without checked-arithmetic failure. -/
theorem row_shape_none (row : U8) (h : 27 ≤ row.val) :
    AspisR1RowShape.r1_wire.row_shape row = ok none := by
  rcases row with ⟨⟨⟨n, hn⟩⟩⟩
  change 27 ≤ n at h
  obtain ⟨k, hk⟩ : ∃ k, n = k + 27 := ⟨n - 27, by omega⟩
  subst n
  simp [AspisR1RowShape.r1_wire.row_shape, UScalar.val, BitVec.toNat]

/-- Total source-result theorem: exact tag and size for every U8 input. -/
theorem row_shape_eq_table (row : U8) :
    AspisR1RowShape.r1_wire.row_shape row = ok (table row) := by
  by_cases h : row.val ≤ 26
  · rcases row with ⟨⟨⟨n, hn⟩⟩⟩
    change n ≤ 26 at h
    interval_cases n <;>
      simp [AspisR1RowShape.r1_wire.row_shape, table, UScalar.val, BitVec.toNat,
        claims_eq, AspisR1RowShape.r1_wire.LANES, claims_plus_lanes_eq,
        claims_payload_eq, lanes_payload_eq, sumcheck_payload_eq]
  · have h27 : 27 ≤ row.val := by omega
    rw [row_shape_none row h27]
    have h2 : row.val ≠ 2 := by omega
    have h14 : row.val ≠ 14 := by omega
    have h25 : row.val ≠ 25 := by omega
    have h26 : row.val ≠ 26 := by omega
    have h13 : ¬row.val ≤ 13 := by omega
    have h24 : ¬row.val ≤ 24 := by omega
    simp [table, h2, h14, h25, h26, h13, h24]

/-- The rejection interval is exact; there are precisely 27 admitted rows. -/
theorem row_shape_none_iff (row : U8) :
    AspisR1RowShape.r1_wire.row_shape row = ok none ↔ 27 ≤ row.val := by
  rw [row_shape_eq_table]
  simp only [Result.ok.injEq]
  unfold table
  split_ifs <;> simp_all <;> omega

end AspisR1.ExtractedRowShape

#print axioms AspisR1.ExtractedRowShape.claims_eq
#print axioms AspisR1.ExtractedRowShape.claims_plus_lanes_eq
#print axioms AspisR1.ExtractedRowShape.claims_payload_eq
#print axioms AspisR1.ExtractedRowShape.lanes_payload_eq
#print axioms AspisR1.ExtractedRowShape.sumcheck_payload_eq

#print axioms AspisR1.ExtractedRowShape.row_shape_none
#print axioms AspisR1.ExtractedRowShape.row_shape_eq_table
#print axioms AspisR1.ExtractedRowShape.row_shape_none_iff
