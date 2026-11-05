"""Own typed source cuts at validation and semantic call occurrences."""
from pathlib import Path
import re,textwrap
E=Path(__file__).resolve().parent
s=(E/'NIY_QueryCut.lean').read_text();params=s[s.index(' (state :'):s.index(' :\n Result')];params=params.replace(' (r34 : verifier.Reader)','')
base='reserved d bytes v end1 i4';args='state a3 a4 val val1 val2 val3 val4 queries'
body=s[s.index(' let r35 ←'):s.index('\n\ntheorem')]
m=re.search(r'(?m)^ (\| core.ops.control_flow.ControlFlow.Continue _ =>)\n',body);assert m
end=re.search(r'(?m)^ \| core.ops.control_flow.ControlFlow.Break',body[m.end():]);assert end
suffix=textwrap.indent(textwrap.dedent(body[m.end():m.end()+end.start()]).rstrip(),' ')
ns='NIY_ValidationCut'
out=f'''import NIY_QueryCut
import NIL_SectionPorts
set_option autoImplicit false
noncomputable section
namespace {ns}
open Aeneas Aeneas.Std Result ControlFlow Error NID_ResumeEmission

def afterValidation (reserved : Bool) {{H : Type}} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
{params} (r34 : verifier.Reader) :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
{suffix}

theorem source (reserved : Bool) {{H : Type}} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
{params} (r34 : verifier.Reader) :
 NIY_QueryCut.afterQueries {base} {args} r34=
 (do let reply ← NIL_FreshOps.validate queries
     NIL_TryTransport.fresh reply (fun _=>afterValidation {base} {args} r34)) := by
 unfold NIY_QueryCut.afterQueries
 apply NIL_ResultCases.bind_congr
 intro reply
 cases reply <;> rfl
#print axioms source
end {ns}
'''
(E/(ns+'.lean')).write_text(out)
