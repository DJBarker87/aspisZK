from pathlib import Path
import re,textwrap,json
E=Path(__file__).resolve().parent
s=(E/'NIY_ValidationCut.lean').read_text();params=s[s.index(' (state :'):s.index(' :\n Result')];params=params.replace(' (r34 : verifier.Reader)','')
base='reserved d bytes v end1 i4';args='state a3 a4 val val1 val2 val3 val4 queries'
body=s[s.index(' let r36 ←'):s.index('\n\ntheorem')]
m=re.search(r'(?m)^ \| core.ops.control_flow.ControlFlow.Continue\s+val5\s*=>\n',body);assert m
end=re.search(r'(?m)^ \| core.ops.control_flow.ControlFlow.Break',body[m.end():]);assert end
suffix=textwrap.dedent(body[m.end():m.end()+end.start()]).rstrip()
suffix=re.sub(r'^let \(semantic_alpha, at1\) := val5\n','',suffix)
suffix=re.sub(r'\{ r34 with «at» := at1 \}', 'rSem',suffix)
ns='NIY_SemanticCut';params+=' (semantic_alpha : Array aspis_core.field.QM31 10#usize)';args+=' semantic_alpha'
header=lambda ns,prior:f'''import {prior}
set_option autoImplicit false
noncomputable section
namespace {ns}
open Aeneas Aeneas.Std Result ControlFlow Error NID_ResumeEmission
'''
pars=lambda params,reader:f'''(reserved : Bool) {{H : Type}} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
{params} ({reader} : verifier.Reader)'''
out=header(ns,'NIY_ValidationCut')+'\ndef suffix '+pars(params,'rSem')+''' :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
'''+textwrap.indent(suffix,' ')+'''\n
theorem source '''+pars(params[:params.index(' (semantic_alpha')],'r34')+f''' :
 NIY_ValidationCut.afterValidation {base} state a3 a4 val val1 val2 val3 val4 queries r34=
 (do let reply ← NIL_FreshOps.semantic bytes r34.«at»
     NIL_TryTransport.fresh reply (fun (semantic_alpha,at1)=>
       suffix {base} {args} {{r34 with «at» := at1}})) := by
 unfold NIY_ValidationCut.afterValidation
 apply NIL_ResultCases.bind_congr
 intro reply
 cases reply with
 | Ok pair => rcases pair with ⟨semantic_alpha,at1⟩;rfl
 | Err err => rfl
#print axioms source
end {ns}
'''
(E/(ns+'.lean')).write_text(out)
prior=ns;reader='rSem'
for label,value,nextreader,op in [('Z0x','val6','r38','readK'),('Z0y','val7','r40','readK'),('Z1x','val8','r42','readK'),('Z1y','val9','r44','readK'),('Claim','val10','r46','readE'),('Rhs','val11','r48','readE'),('Power','val12','r50','readK')]:
 s=(E/(prior+'.lean')).read_text();start=s.index(' := do\n')+len(' := do\n');finish=s.index('\n\ntheorem',start);body=s[start:finish]
 # Allow the extracted emitter's multiline `|` formatting.
 m=re.search(r'(?m)^( *)\|\s*core.ops.control_flow.ControlFlow.Continue\s+'+value+r'\s*=>\n',body);assert m,label
 indent=len(m[1]);b=re.search(r'(?m)^'+(' '*indent)+r'\|\s*core.ops.control_flow.ControlFlow.Break',body[m.end():]);assert b,label
 suffix=textwrap.indent(textwrap.dedent(body[m.end():m.end()+b.start()]).rstrip(),' ')
 ns='NIY_After'+label;typ='aspis_core.field.QM31' if op=='readK' else 'aspis_core.field.wide_exact.WideExact'
 newparams=params+' ('+value+' : '+typ+')';newargs=args+' '+value
 out=header(ns,prior)+'\ndef suffix '+pars(newparams,nextreader)+''' :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
'''+suffix+'\n\ntheorem source '+pars(params,reader)+f''' :
 {prior}.suffix {base} {args} {reader}=
 (do let (reply,out) ← NIL_FreshOps.{op} {reader}
     NIL_TryTransport.fresh reply (fun x=>suffix {base} {args} x out)) := by
 unfold {prior}.suffix
 apply NIL_ResultCases.bind_congr
 rintro ⟨reply,out⟩
 cases reply <;> rfl
#print axioms source
end {ns}
'''
 (E/(ns+'.lean')).write_text(out)
 params=newparams;args=newargs;reader=nextreader;prior=ns
(E/'NIY_LOWER_CONTEXT.json').write_text(json.dumps(dict(params=params,args=args,reader=reader),indent=2)+'\n')
