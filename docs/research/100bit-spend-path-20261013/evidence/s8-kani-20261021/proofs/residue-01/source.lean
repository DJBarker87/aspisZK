import S8OwnedP6ValueModel
import S7OwnedP6RowContract

set_option autoImplicit false
namespace S8OwnedP6Residue
open Aeneas Aeneas.Std Result
open S8OwnedP6 S8OwnedP6ValueModel

/-- Complete emitted four-lane residue update, with the exact four-query
phase invariant supplying all checked product/addition bounds. -/
theorem residue_total_model (row : Row) (power : Q) (basis : U32) (terms : Nat)
    (hl : ∀ j : Fin 4, (coordinate power j).val<2^31-1)
    (hb : basis.val<2^31-1)
    (hr : ∀ j : Fin 4, (rowAt row j).val<2^34+(terms%4)*(2^31-2)^2) :
    ∃ out : Row,
      residue_owned row power basis (decide (terms%4=3))=.ok out ∧
      ∀ j : Fin 4, (rowAt out j).val=
        AspisR1BatchedFoldSourceStep.sourcePush terms (rowAt row j).val
          ((coordinate power j).val*basis.val) := by
  obtain ⟨x0,h0,v0⟩ := WP.spec_imp_exists (Array.index_usize_spec row 0#usize (by simp [row.property]))
  obtain ⟨x1,h1,v1⟩ := WP.spec_imp_exists (Array.index_usize_spec row 1#usize (by simp [row.property]))
  obtain ⟨x2,h2,v2⟩ := WP.spec_imp_exists (Array.index_usize_spec row 2#usize (by simp [row.property]))
  obtain ⟨x3,h3,v3⟩ := WP.spec_imp_exists (Array.index_usize_spec row 3#usize (by simp [row.property]))
  have b0 : x0.val<2^34+(terms%4)*(2^31-2)^2 := by simpa [rowAt,v0] using hr 0
  have b1 : x1.val<2^34+(terms%4)*(2^31-2)^2 := by simpa [rowAt,v1] using hr 1
  have b2 : x2.val<2^34+(terms%4)*(2^31-2)^2 := by simpa [rowAt,v2] using hr 2
  have b3 : x3.val<2^34+(terms%4)*(2^31-2)^2 := by simpa [rowAt,v3] using hr 3
  obtain ⟨z0,r0,e0⟩ := residue_scalar_model x0 power.c0.a basis terms (hl 0) hb b0
  obtain ⟨z1,r1,e1⟩ := residue_scalar_model x1 power.c0.b basis terms (hl 1) hb b1
  obtain ⟨z2,r2,e2⟩ := residue_scalar_model x2 power.c1.a basis terms (hl 2) hb b2
  obtain ⟨z3,r3,e3⟩ := residue_scalar_model x3 power.c1.b basis terms (hl 3) hb b3
  refine ⟨Array.make 4#usize [z0,z1,z2,z3],?_,?_⟩
  · simp only [residue_owned,h0,h1,h2,h3,r0,r1,r2,r3,bind_tc_ok]
  · intro j
    fin_cases j
    · simpa [rowAt,coordinate,Array.make,v0] using e0
    · simpa [rowAt,coordinate,Array.make,v1] using e1
    · simpa [rowAt,coordinate,Array.make,v2] using e2
    · simpa [rowAt,coordinate,Array.make,v3] using e3

/-- The two-pass frozen row order has the same model as the emitted fused
reference. This reuses the proved S7 order/frame contract, not a timed-out
whole-row solver. -/
theorem frozen_row_model (row limbs : S7OwnedP6RowContract.Row) (basis terms : Nat) :
    S7OwnedP6RowContract.source row limbs basis (decide (terms%4=3))=
      fun j => AspisR1BatchedFoldSourceStep.sourcePush terms (row j) (limbs j*basis) :=
  S7OwnedP6RowContract.source_eq_batched_model row limbs basis terms

#print axioms residue_total_model
#print axioms frozen_row_model
end S8OwnedP6Residue
