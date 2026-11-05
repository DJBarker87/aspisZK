from pathlib import Path
import re,textwrap,json
E=Path(__file__).resolve().parent
s=(E/'NIY_AfterRho.lean').read_text();a=s.index(' let (a5, r13) ←');b=s.index(' let r35 ←',a)
chunk=s[a:b].rstrip();words=', '.join('i'+str(i) for i in range(8,30));arr='(Array.make 22#usize ['+words+'])'
rawchunk=chunk.replace('NIL_FreshOps.raw 4#usize','raw')
header='''import NIY_RawTransport
set_option autoImplicit false
noncomputable section
namespace NIY_QueryRead
open Aeneas Aeneas.Std Result

/-- Result associativity, including outer fail and divergence. -/
theorem assoc {A B C : Type} (m : Result A) (f : A → Result B) (g : B → Result C) :
 (do let y ← (do let x ← m;f x);g y)=(do let x ← m;let y ← f x;g y) := by
 cases m <;> rfl

def read22 {R : Type} (raw : R → Result (Array U8 4#usize × R)) (r12 : R) :
 Result (Array U32 22#usize × R) := do
'''
body=header+rawchunk+'\n ok ('+arr+',r34)\n\n'
body+='''/-- Named ordered query continuation; the SAME final reader is passed to next. -/
theorem continuation {R A : Type} (raw : R → Result (Array U8 4#usize × R))
 (r12 : R) (next : Array U32 22#usize → R → Result A) :
 (do let (queries,out) ← read22 raw r12;next queries out)=(do
'''+textwrap.indent(rawchunk,' ')+f'\n  next {arr} r34) := by\n simp only [read22,assoc]\n\n#print axioms assoc\n#print axioms continuation\nend NIY_QueryRead\n'
(E/'NIY_QueryRead.lean').write_text(body)
# Tail uses a named query array at both occurrences.
rem=s[b:s.index('\n\ntheorem',b)]
rem,n=re.subn(r'\(Array\.make\s+22#usize\s*\[\s*i8,.*?i29\s*\]\)', 'queries',rem,flags=re.S);assert n==2,n
ctx=json.loads((E/'NIY_TYPED_CONTEXT.json').read_text());params=' '.join('('+n+' : '+t+')' for n,t in zip(ctx['ctx'],ctx['types']));args=' '.join(ctx['ctx']);base='reserved d bytes v end1 i4'
out=f'''import NIY_AfterRho
import NIY_QueryRead
set_option autoImplicit false
noncomputable section
namespace NIY_QueryCut
open Aeneas Aeneas.Std Result ControlFlow Error NID_ResumeEmission

def afterQueries (reserved : Bool) {{H : Type}} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 {params} (queries : Array U32 22#usize) (r34 : verifier.Reader) :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
{rem}

theorem source (reserved : Bool) {{H : Type}} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 {params} (r12 : verifier.Reader) :
 NIY_AfterRho.suffix {base} {args} r12=
 (do let (queries,out) ← NIY_QueryRead.read22 (NIL_FreshOps.raw 4#usize) r12
     afterQueries {base} {args} queries out) := by
 rw [NIY_QueryRead.continuation]
 unfold NIY_AfterRho.suffix
 repeat' first
  | (with_unfolding_all apply NIL_ResultCases.bind_congr; intro x)
  | (with_unfolding_all apply NIL_SpineCongr.prod; intro x y)
  | rfl
#print axioms source
end NIY_QueryCut
'''
(E/'NIY_QueryCut.lean').write_text(out)
