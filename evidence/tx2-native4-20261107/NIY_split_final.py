from pathlib import Path
import re,textwrap,json
E=Path(__file__).resolve().parent;s=(E/'NIY_AfterPower.lean').read_text();ctx=json.loads((E/'NIY_LOWER_CONTEXT.json').read_text());params=ctx['params'];args=ctx['args'];base='reserved d bytes v end1 i4'
body=s[s.index(' := do\n')+len(' := do\n'):s.index('\n\ntheorem')]
m=re.search(r'(?m)^( *)\|\s*core.ops.control_flow.ControlFlow.Continue\s+val13\s*=>\n',body);assert m
indent=len(m[1]);b=re.search(r'(?m)^'+(' '*indent)+r'\|\s*core.ops.control_flow.ControlFlow.Break',body[m.end():]);assert b
suffix=textwrap.indent(textwrap.dedent(body[m.end():m.end()+b.start()]).rstrip(),' ')
ns='NIY_AllocationCut';newparams=params+' (val13 : alloc.vec.Vec aspis_core.field.QM31)'
header=lambda ns,prior:f'''import {prior}
import NIL_AllocationPort
set_option autoImplicit false
noncomputable section
namespace {ns}
open Aeneas Aeneas.Std Result ControlFlow Error NID_ResumeEmission
'''
pars=lambda params,reader:f'''(reserved : Bool) {{H : Type}} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
{params} ({reader} : verifier.Reader)'''
out=header(ns,'NIY_AfterPower')+'\ndef suffix '+pars(newparams,'r50')+''' :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
'''+suffix+'\n\ntheorem source '+pars(params,'r50')+f''' :
 NIY_AfterPower.suffix {base} {args} r50=
 (do
   let n ← AspisR1.CheckpointBytes4Ops.finalLen (NIL_Carriers.variant v)
   let zero ← (ok (NIL_Carriers.unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
   let reply ← NIL_FreshOps.filled reserved
     (aspis_core.field.QM31.Insts.CoreMarkerCopy (fun x=>ok x)) n zero
   let converted ← NIL_FreshOps.mapError
     (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError (NIL_FreshOps.digest d)) reply ()
   NIL_TryTransport.fresh converted (fun weights=>suffix {base} {args} weights r50)) := by
 unfold NIY_AfterPower.suffix
 apply NIL_ResultCases.bind_congr
 intro n
 apply NIL_ResultCases.bind_congr
 intro zero
 apply NIL_ResultCases.bind_congr
 intro reply
 apply NIL_ResultCases.bind_congr
 intro converted
 cases converted <;> rfl
#print axioms source
end {ns}
'''
(E/(ns+'.lean')).write_text(out)
# Cut the returned weights/offset pair without reselecting either.
body=suffix;m=re.search(r'(?m)^( *)\|\s*core.ops.control_flow.ControlFlow.Continue\s+val14\s*=>\n',body);assert m
indent=len(m[1]);b=re.search(r'(?m)^'+(' '*indent)+r'\|\s*core.ops.control_flow.ControlFlow.Break',body[m.end():]);assert b
final=textwrap.dedent(body[m.end():m.end()+b.start()]).rstrip();final=final.removeprefix('let (weights, at2) := val14\n')
ns='NIY_FinalCut';p=params+' (weights : alloc.vec.Vec aspis_core.field.QM31) (at2 : Usize)'
finalparams=pars(p,'r50'); # r50 unused in final result, retained for source frame identity.
out=header(ns,'NIY_AllocationCut')+'\ndef finish '+finalparams+''' :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
'''+textwrap.indent(final,' ')+'\n\ntheorem source '+pars(newparams,'r50')+f''' :
 NIY_AllocationCut.suffix {base} {args} val13 r50=
 (do let reply ← NIL_FreshOps.weights bytes r50.«at» val13
     NIL_TryTransport.fresh reply (fun (weights,at2)=>finish {base} {args} weights at2 r50)) := by
 unfold NIY_AllocationCut.suffix
 apply NIL_ResultCases.bind_congr
 intro reply
 cases reply with
 | Ok pair => rcases pair with ⟨weights,at2⟩;rfl
 | Err err => rfl
#print axioms source
end {ns}
'''
(E/(ns+'.lean')).write_text(out)
