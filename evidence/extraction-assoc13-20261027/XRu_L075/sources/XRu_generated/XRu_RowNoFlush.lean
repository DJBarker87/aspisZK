import XRu_RowRun
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRu_RowNoFlush
open XRu_RowShape
/-- The complete no-flush emitted row agrees with the owned model on its
actual four-limb no-overflow domain. No successful alternate row is assumed. -/
theorem source (row : Row) (power : aspis_core.field.QM31) (basis : U32)
 (safe : ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
  raw.val+(S7Kani2OwnedRow.limb ⟨(power.c0.a,power.c0.b),(power.c1.a,power.c1.b)⟩ j).val*basis.val<2^64) :
 verifier.update_residue_row row power basis false=
 S7Kani2OwnedRow.residue_owned row ⟨(power.c0.a,power.c0.b),(power.c1.a,power.c1.b)⟩ basis false := by
 obtain ⟨a,b,c,d,shape⟩ := cells row
 subst row
 have s0 := safe 0#usize a (by decide) rfl
 have s1 := safe 1#usize b (by decide) rfl
 have s2 := safe 2#usize c (by decide) rfl
 have s3 := safe 3#usize d (by decide) rfl
 simp [S7Kani2OwnedRow.limb] at s0 s1 s2 s3
 obtain ⟨x0,h0,_⟩ := S7OwnedP6ScalarProof.scalar_success a power.c0.a basis false s0
 obtain ⟨x1,h1,_⟩ := S7OwnedP6ScalarProof.scalar_success b power.c0.b basis false s1
 obtain ⟨x2,h2,_⟩ := S7OwnedP6ScalarProof.scalar_success c power.c1.a basis false s2
 obtain ⟨x3,h3,_⟩ := S7OwnedP6ScalarProof.scalar_success d power.c1.b basis false s3
 have run := XRu_RowRun.source a b c d x0 x1 x2 x3 power.c0.a power.c0.b power.c1.a power.c1.b basis h0 h1 h2 h3
 unfold verifier.update_residue_row
 rw [run,bind_tc_ok]
 change ok (Array.make 4#usize [x0,x1,x2,x3])=_
 unfold S7Kani2OwnedRow.residue_owned
 change _=(do
  let y0 ← S7OwnedP6Scalar.residue_scalar_owned a power.c0.a basis false
  let y1 ← S7OwnedP6Scalar.residue_scalar_owned b power.c0.b basis false
  let y2 ← S7OwnedP6Scalar.residue_scalar_owned c power.c1.a basis false
  let y3 ← S7OwnedP6Scalar.residue_scalar_owned d power.c1.b basis false
  ok (Array.make 4#usize [y0,y1,y2,y3]))
 rw [h0,bind_tc_ok,h1,bind_tc_ok,h2,bind_tc_ok,h3]
 rfl
#print axioms source
end XRu_RowNoFlush
