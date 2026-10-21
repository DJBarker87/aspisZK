import S7Kani2AccumulatorLoop
import S7OwnedP6ScalarProof

/- Literal emitted four-scalar row, ported only across the recorded structural
carrier renaming. Every array read and scalar operation is checked. -/
set_option autoImplicit false
namespace S7Kani2OwnedRow
open Aeneas Aeneas.Std Result
open AspisV8R17.RawReducer
abbrev K := S7Kani2AccumulatorLoop.K
abbrev Row := Array U64 4#usize

def limb (power : K) (j : Usize) : U32 :=
  if j=0#usize then power.c0.1 else if j=1#usize then power.c0.2
  else if j=2#usize then power.c1.1 else power.c1.2

def residue_owned
  (row : Array Std.U64 4#usize) (power : S7Kani2AccumulatorLoop.K)
  (basis : U32) (flush : Bool) :
  Result (Array Std.U64 4#usize)
  := do
  let i ← Array.index_usize row 0#usize
  let i1 := power.c0.1
  let i2 ← S7OwnedP6Scalar.residue_scalar_owned i i1 basis flush
  let i3 ← Array.index_usize row 1#usize
  let i4 := power.c0.2
  let i5 ← S7OwnedP6Scalar.residue_scalar_owned i3 i4 basis flush
  let i6 ← Array.index_usize row 2#usize
  let i7 := power.c1.1
  let i8 ← S7OwnedP6Scalar.residue_scalar_owned i6 i7 basis flush
  let i9 ← Array.index_usize row 3#usize
  let i10 := power.c1.2
  let i11 ← S7OwnedP6Scalar.residue_scalar_owned i9 i10 basis flush
  ok (Array.make 4#usize [ i2, i5, i8, i11 ])

/-- Total four-lane source execution, without arithmetic callee premises.
The local overflow invariant is explicit and supplied by phase_bound. -/
theorem row_total (row : Row) (power : K) (basis : U32) (flush : Bool)
    (safe : ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
      raw.val+(limb power j).val*basis.val<2^64) :
    ∃ out, residue_owned row power basis flush=ok out := by
  obtain ⟨r0,h0,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec row 0#usize (by scalar_tac))
  obtain ⟨r1,h1,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec row 1#usize (by scalar_tac))
  obtain ⟨r2,h2,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec row 2#usize (by scalar_tac))
  obtain ⟨r3,h3,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec row 3#usize (by scalar_tac))
  have s0 := safe 0#usize r0 (by decide) h0
  have s1 := safe 1#usize r1 (by decide) h1
  have s2 := safe 2#usize r2 (by decide) h2
  have s3 := safe 3#usize r3 (by decide) h3
  simp only [limb] at s0 s1 s2 s3
  obtain ⟨x0,hx0,_⟩ := S7OwnedP6ScalarProof.scalar_success r0 power.c0.1 basis flush s0
  obtain ⟨x1,hx1,_⟩ := S7OwnedP6ScalarProof.scalar_success r1 power.c0.2 basis flush s1
  obtain ⟨x2,hx2,_⟩ := S7OwnedP6ScalarProof.scalar_success r2 power.c1.1 basis flush s2
  obtain ⟨x3,hx3,_⟩ := S7OwnedP6ScalarProof.scalar_success r3 power.c1.2 basis flush s3
  exact ⟨_,by simp only [residue_owned,h0,h1,h2,h3,hx0,hx1,hx2,hx3,bind_tc_ok]⟩

#print axioms row_total
end S7Kani2OwnedRow
