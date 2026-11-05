"""Own literal Lean continuation splitter; each association is separately kernel checked."""
from pathlib import Path
import re,textwrap,json
E=Path(__file__).resolve().parent
ctx=['state','a3','a4','val'];types=['Array U8 32#usize']*3+['aspis_core.field.wide_exact.WideExact']
reader='r4';prior='NIY_FirstECut';priorfun='afterGamma'
for label,value,nextreader in [('Kappa','val1','r6'),('Alpha0','val2','r8'),('Alpha1','val3','r10'),('Rho','val4','r12')]:
 s=(E/(prior+'.lean')).read_text();start=s.index(' := do\n')+len(' := do\n');finish=s.index('\n\ntheorem',start);body=s[start:finish]
 m=re.search(r'(?m)^( *)\| core.ops.control_flow.ControlFlow.Continue\s+'+value+r'\s*=>\n',body);assert m,(label,body[:200])
 indent=len(m[1]);b=re.search(r'(?m)^'+(' '*indent)+r'\| core.ops.control_flow.ControlFlow.Break',body[m.end():]);assert b
 suffix=textwrap.indent(textwrap.dedent(body[m.end():m.end()+b.start()]).rstrip(),' ')
 ns='NIY_After'+label;typ='aspis_core.field.QM31' if label=='Rho' else 'aspis_core.field.wide_exact.WideExact'
 context=' '.join('('+n+' : '+t+')' for n,t in zip(ctx,types));newcontext=context+' ('+value+' : '+typ+')';base='reserved d bytes v end1 i4';args=' '.join(ctx)
 out=f'''import {prior}
set_option autoImplicit false
noncomputable section
namespace {ns}
open Aeneas Aeneas.Std Result ControlFlow Error NID_ResumeEmission

def suffix (reserved : Bool) {{H : Type}} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 {newcontext} ({nextreader} : verifier.Reader) :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
{suffix}

theorem source (reserved : Bool) {{H : Type}} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 {context} ({reader} : verifier.Reader) :
 {prior}.{priorfun} {base} {args} {reader}=
 (do let (reply,out) ← NIL_FreshOps.{'readK' if label=='Rho' else 'readE'} {reader}
     NIL_TryTransport.fresh reply (fun x=>suffix {base} {args} x out)) := by
 unfold {prior}.{priorfun}
 apply NIL_ResultCases.bind_congr
 rintro ⟨reply,out⟩
 cases reply <;> rfl
#print axioms source
end {ns}
'''
 (E/(ns+'.lean')).write_text(out)
 ctx+=[value];types+=[typ];reader=nextreader;prior=ns;priorfun='suffix'
(E/'NIY_TYPED_CONTEXT.json').write_text(json.dumps(dict(ctx=ctx,types=types,reader=reader),indent=2)+'\n')
