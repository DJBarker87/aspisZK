import XRu_RowBoth
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRu_RowNonvacuity
open XRu_RowShape
/-- The equality's local domain supplies both successful computations. -/
theorem total (row : Row) (q : aspis_core.field.QM31) (basis : U32) (flush : Bool)
 (safe : ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
  raw.val+(S7Kani2OwnedRow.limb ⟨(q.c0.a,q.c0.b),(q.c1.a,q.c1.b)⟩ j).val*basis.val<2^64) :
 ∃ out, verifier.update_residue_row row q basis flush=ok out ∧
 S7Kani2OwnedRow.residue_owned row ⟨(q.c0.a,q.c0.b),(q.c1.a,q.c1.b)⟩ basis flush=ok out := by
 obtain ⟨out,run⟩ := S7Kani2OwnedRow.row_total row _ basis flush safe
 exact ⟨out,(XRu_RowBoth.source row q basis flush safe).trans run,run⟩
/-- A zero basis inhabits the domain for EVERY raw row, not just a fixture. -/
theorem zero_domain (row : Row) (q : aspis_core.field.QM31) :
 ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
 raw.val+(S7Kani2OwnedRow.limb ⟨(q.c0.a,q.c0.b),(q.c1.a,q.c1.b)⟩ j).val*(0#u32).val<2^64 := by
 intro j raw _ _
 have h := raw.bv.isLt
 change raw.val<2^64 at h
 simpa using h
#print axioms total
#print axioms zero_domain
end XRu_RowNonvacuity
