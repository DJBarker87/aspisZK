from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
p=B/'evidence/s7-kani-20261021/extraction/generated/S7OwnedP6/Funs.lean';s=p.read_text();a=s.index('def residue_owned\n');b=s.index('\n/--',a);original=s[a:b]
body=original.replace('aspis_core.field.QM31','S7Kani2AccumulatorLoop.K').replace('aspis_core.field.M31','U32').replace('power.c0.a','power.c0.1').replace('power.c0.b','power.c0.2').replace('power.c1.a','power.c1.1').replace('power.c1.b','power.c1.2').replace('residue_scalar_owned','S7OwnedP6Scalar.residue_scalar_owned')
header='''import S7Kani2AccumulatorLoop
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

'''
tail='''
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
  simp [limb] at s0 s1 s2 s3
  obtain ⟨x0,hx0,_⟩ := S7OwnedP6ScalarProof.scalar_success r0 power.c0.1 basis flush s0
  obtain ⟨x1,hx1,_⟩ := S7OwnedP6ScalarProof.scalar_success r1 power.c0.2 basis flush s1
  obtain ⟨x2,hx2,_⟩ := S7OwnedP6ScalarProof.scalar_success r2 power.c1.1 basis flush s2
  obtain ⟨x3,hx3,_⟩ := S7OwnedP6ScalarProof.scalar_success r3 power.c1.2 basis flush s3
  exact ⟨Array.make 4#usize [x0,x1,x2,x3],by simp [residue_owned,h0,h1,h2,h3,hx0,hx1,hx2,hx3]⟩

#print axioms row_total
end S7Kani2OwnedRow
'''
text=header+body+tail;out=B/'lean/S7Kani2OwnedRow.lean'
if '--check' in sys.argv:assert out.read_text()==text
else:out.write_text(text)
(B/'evidence/s7-kani2-20261021/row-binding.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),declaration_sha256=hashlib.sha256(original.encode()).hexdigest(),edits='Explicit structural carrier names K.c0/c1 pair projections; scalar function qualified to previously checked exact declaration. No source operations removed.'),indent=2)+'\n')
