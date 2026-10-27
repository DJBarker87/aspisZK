import XRu_RowNoFlush
import XRu_RowFoldRun
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRu_RowBoth
open XRu_RowShape
/-- Exact scalar sequencing equation, retaining checked Result behavior. -/
theorem scalar (a : U64) (limb basis : U32) :
 S7OwnedP6Scalar.residue_scalar_owned a limb basis true =
 (do let sum ← S7OwnedP6Scalar.residue_scalar_owned a limb basis false
     AspisR1.ExtractedCurrentReducer.foldExecution sum) := by
 simp only [S7OwnedP6Scalar.residue_scalar_owned,
  AspisR1.ExtractedCurrentReducer.foldExecution,
  AspisR1.ExtractedCurrentReducer.mask64,AspisR1.ExtractedCurrentReducer.mask32,
  lift,bind_tc_ok,bind_assoc_eq]
 rfl
#print axioms scalar
/-- Both actual flush phases agree with the SAME four-cell owned model;
the caller still owes this no-overflow domain at every reached prefix. -/
theorem source (row : Row) (power : aspis_core.field.QM31) (basis : U32) (flush : Bool)
 (safe : ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
  raw.val+(S7Kani2OwnedRow.limb ⟨(power.c0.a,power.c0.b),(power.c1.a,power.c1.b)⟩ j).val*basis.val<2^64) :
 verifier.update_residue_row row power basis flush=
 S7Kani2OwnedRow.residue_owned row ⟨(power.c0.a,power.c0.b),(power.c1.a,power.c1.b)⟩ basis flush := by
 cases flush with
 | false => exact XRu_RowNoFlush.source row power basis safe
 | true =>
  obtain ⟨a,b,c,d,shape⟩ := cells row
  subst row
  have s0 := safe 0#usize a (by decide) rfl
  have s1 := safe 1#usize b (by decide) rfl
  have s2 := safe 2#usize c (by decide) rfl
  have s3 := safe 3#usize d (by decide) rfl
  simp [S7Kani2OwnedRow.limb] at s0 s1 s2 s3
  obtain ⟨x0,h0,_⟩ := S7OwnedP6ScalarProof.scalar_success a power.c0.a basis false s0
  obtain ⟨y0,f0,_⟩ := AspisR1.ExtractedCurrentReducer.foldExecution_success x0
  have t0 : S7OwnedP6Scalar.residue_scalar_owned a power.c0.a basis true=ok y0 := by
   rw [scalar,h0,bind_tc_ok,f0]
  obtain ⟨x1,h1,_⟩ := S7OwnedP6ScalarProof.scalar_success b power.c0.b basis false s1
  obtain ⟨y1,f1,_⟩ := AspisR1.ExtractedCurrentReducer.foldExecution_success x1
  have t1 : S7OwnedP6Scalar.residue_scalar_owned b power.c0.b basis true=ok y1 := by
   rw [scalar,h1,bind_tc_ok,f1]
  obtain ⟨x2,h2,_⟩ := S7OwnedP6ScalarProof.scalar_success c power.c1.a basis false s2
  obtain ⟨y2,f2,_⟩ := AspisR1.ExtractedCurrentReducer.foldExecution_success x2
  have t2 : S7OwnedP6Scalar.residue_scalar_owned c power.c1.a basis true=ok y2 := by
   rw [scalar,h2,bind_tc_ok,f2]
  obtain ⟨x3,h3,_⟩ := S7OwnedP6ScalarProof.scalar_success d power.c1.b basis false s3
  obtain ⟨y3,f3,_⟩ := AspisR1.ExtractedCurrentReducer.foldExecution_success x3
  have t3 : S7OwnedP6Scalar.residue_scalar_owned d power.c1.b basis true=ok y3 := by
   rw [scalar,h3,bind_tc_ok,f3]
  have run := XRu_RowRun.source a b c d x0 x1 x2 x3 power.c0.a power.c0.b power.c1.a power.c1.b basis h0 h1 h2 h3
  have folded := XRu_RowFoldRun.restore x0 x1 x2 x3 y0 y1 y2 y3 f0 f1 f2 f3
  unfold verifier.update_residue_row
  dsimp only
  rw [run,bind_tc_ok]
  change (do
   let (iter,intoBack) ← XRn_Join_intoIter (XRu_RowFold.row x0 x1 x2 x3)
   let back ← verifier.update_residue_row_loop1 iter id
   ok (intoBack back))=_
  refine folded.trans ?_
  unfold S7Kani2OwnedRow.residue_owned
  change _=(do
   let z0 ← S7OwnedP6Scalar.residue_scalar_owned a power.c0.a basis true
   let z1 ← S7OwnedP6Scalar.residue_scalar_owned b power.c0.b basis true
   let z2 ← S7OwnedP6Scalar.residue_scalar_owned c power.c1.a basis true
   let z3 ← S7OwnedP6Scalar.residue_scalar_owned d power.c1.b basis true
   ok (Array.make 4#usize [z0,z1,z2,z3]))
  rw [t0,bind_tc_ok,t1,bind_tc_ok,t2,bind_tc_ok,t3]
  rfl
#print axioms source
end XRu_RowBoth
