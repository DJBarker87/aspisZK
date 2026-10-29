"""Factor the exact successful-material continuation, retaining its Result calls."""
from pathlib import Path
import hashlib,json,textwrap,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin48-20261029';D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
p=json.loads((E/'build-plan.json').read_text())['modules']['R1Z.ProverRwFullFuns'];assert hashlib.sha256((R/p['path']).read_bytes()).hexdigest()==p['sha256']
s=(D/'PV_RunJoin_PrepareDomainContext48.lean').read_text();a=s.index('def run\n');z=s.index('\n\ntheorem source',a);body=s[a:z];a=body.index('        let s6 := alloc.vec.Vec.deref q');z=body.index('\n      | core.ops.control_flow.ControlFlow.Break residual =>',a);suffix=body[a:z]
tail=textwrap.dedent(suffix)
for n in ['s6','s10']:
 tail=tail.replace('let '+n+' := alloc.vec.Vec.deref q\n','let '+n+' := q\n')
for n in ['s7','s11']:
 tail=tail.replace('let '+n+' := alloc.vec.Vec.deref val1\n','let '+n+' := w\n')
head='''import R1Z.PV_RunJoin_PreparedDomain48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareTail48
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact

def run (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript2 : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa : W) (q w : Slice W) :
    Result (core.result.Result prover.PreparedOpening verifier.Error) := do
'''
out=head+textwrap.indent(tail,'  ')+'''
#print axioms run
end R1Z.PV_RunJoin_PrepareTail48
'''
context=body[:a]+'''        PV_RunJoin_PrepareTail48.run variant hash backend sem transcript2 y1 gamma inactive kappa
          (alloc.vec.Vec.deref q) (alloc.vec.Vec.deref val1)'''+body[z:]
context='''import R1Z.PV_RunJoin_PrepareDomainContext48
import R1Z.PV_RunJoin_PrepareTail48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareTailContext48
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

'''+context+'''

theorem source (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (backend : prover.Backend)
    (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (coefficients : Result (alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize)))
    (constructor : Result (core.result.Result weights.Weights verifier.Error))
    (materialize : weights.Weights → aspis_core.field.wide_exact.WideExact →
      Result (core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) verifier.Error)) :
    PV_RunJoin_PrepareDomainContext48.run variant hash backend sem coefficients constructor materialize=
      run variant hash backend sem coefficients constructor materialize := by rfl
#print axioms source
end R1Z.PV_RunJoin_PrepareTailContext48
'''
for name,content in [('PrepareTail48',out),('PrepareTailContext48',context)]:
 path=D/('PV_RunJoin_'+name+'.lean')
 if '--check' in sys.argv:assert path.read_text()==content
 else:path.write_text(content)
(E/'prepare-tail-source-identity.json').write_text(json.dumps(dict(frozen_source=p,domain_context_sha256=hashlib.sha256(s.encode()).hexdigest(),original_suffix_sha256=hashlib.sha256(suffix.encode()).hexdigest(),changes=['factor only material-success continuation','pass exact dereferenced q and w without changing their reads'],outputs={n:hashlib.sha256(v.encode()).hexdigest() for n,v in [('PrepareTail48',out),('PrepareTailContext48',context)]}),indent=2)+'\n')
