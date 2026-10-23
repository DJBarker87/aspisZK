#!/usr/bin/env python3
"""Pin actual source items and check retained emitted constructor normalization."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/ports3-20261023'
L=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((E/'source-body-inventory.json').read_text())
def item(s,marker):
 a=s.index(marker);b=s.index('{',a);d=1;i=b+1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
for row in inv['rows']:
 s=item((R/row['path']).read_text(),row['marker'])
 assert hashlib.sha256(s.encode()).hexdigest()==row['current_body_sha256'],row['op']
 assert row['identical_to_b2727acd3']
origin=R/'docs/research/100bit-spend-path-20261013/evidence/s4-accumulator-new-current-extraction-v1-20261021/sources/AspisR1S4AccumulatorNewWrapperV11Probe/Funs.lean'
s=origin.read_text();a=s.index('def verifier.Accumulator.new\n');b=s.index('/-- [aspis_r1_cost_probe::verifier::accumulator_new_probe]',a);s=s[a:b];s=s[s.index(':= do')+5:]
t=(L/'Port3_Constructor.lean').read_text();a=t.index('def extracted ');b=t.index('\ntheorem map_error_exact',a);t=t[a:b];t=t[t.index(':= do')+5:]
replacements={'transport.Variant.final_len v':'ops.finalLen v',
 'aspis_core.field.QM31.ZERO':'ops.zero',
 'aspis_core.r0.heap.filled aspis_core.field.QM31.Insts.CoreMarkerCopy':'ops.filled ops.copy',
 'verifier.Accumulator.new.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError':'allocationError',
 'aspis_core.field.wide_exact.WideExact.ZERO':'ops.zeroWide',
 'aspis_core.field.QM31.ONE':'ops.one','core.result.Result.Ok':'.Ok'}
s=' '.join(s.split())
for old,new in replacements.items():s=s.replace(old,new)
n=lambda x:re.sub(r'\s+','',x)
assert n(s)==n(t),'emitted instruction mismatch'
# Reference roots are NOT the same Rust functions as the shipped parents.
references=[(6,'tools/s7-kani-20261021/src/owned.rs','pub fn query_loop_owned('),
 (8,'tools/oracle-port-ckpt-abi2/src/lib.rs','fn body_byte('),
 (9,'tools/s8-kani-20261021/src/owned.rs','pub fn finish_owned('),
 (11,'tools/s7-kani-20261021/src/geometry_owned.rs','fn geometry_owned(')]
refs=[]
for op,path,marker in references:
 body=item((R/path).read_text(),marker);native=next(r for r in inv['rows'] if r['op']==op)
 h=hashlib.sha256(body.encode()).hexdigest()
 assert h!=native['current_body_sha256']
 refs.append({'op':op,'reference_file':path,'reference_marker':marker,'reference_body_sha256':h,
  'native_body_sha256':native['current_body_sha256'],'identical_source_bodies':False,
  'meaning':'Different source root; requires named P6 correspondence, not D188 alone'})
files=['Cargo.toml','Cargo.lock','crates/aspis-r1-cost-probe/src/candidate.rs',
 'crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/transport.rs',
 'crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs',
 'programs/r1-cost-probe/src/r1_pool_adapter.rs']
for f in files:
 assert (R/f).read_bytes()==subprocess.check_output(['git','show',inv['revision']+':'+f],cwd=R),f
result={'schema':'ports3-source-normalization-v1','base_revision':inv['revision'],
 'constructor_emission':str(origin.relative_to(R)),'constructor_emission_sha256':sha(origin),
 'constructor_instruction_normalization':True,'normalization_replacements':replacements,
 'kernel_normalization_theorem':'AspisR1.Port3_Constructor.normalization',
 'reference_root_comparisons':refs,'current_source_pins':{f:sha(R/f) for f in files},
 'h5_assessment':'Body-local identity only. No historical backend theorem is reassigned. Current raw zero/one interpretation is proved independently in Port3_Constants; arithmetic operations remain owner obligations.',
 'shipped_delta':[]}
(E/'source-normalization.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: nine native body pins; exact emitted constructor normalization; four reference roots correctly distinguished; no shipped change')
