#!/usr/bin/env python3
"""Check source-only Claims extraction/getter/accepted-parent evidence; no replay."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=E/'s1-claims-unrolled-source-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
for rel,h in m['files'].items():
 p=R/rel;assert sha(p)==h,rel
 assert p.suffix not in ['.olean','.ilean','.llbc','.rlib','.rmeta','.goto','.o','.a','.so'],rel
for phase in ['charon','aeneas']:
 d=E/'s1-claims-nuc-extract-run10';j=json.loads((d/(phase+'-receipt.json')).read_text())
 assert j['exit_status']==0 and j['source_unchanged'] and j['tools_unchanged']
 cg=j['cgroup_values'];assert cg['memory.max']=='6442450944' and cg['memory.high']=='4294967296' and cg['memory.swap.max']=='0' and cg['memory.oom.group']=='1'
 assert 'oom_kill 0' in cg['memory.events'] and '\tSwaps: 0' in (d/(phase+'-time.log')).read_text()
assert json.loads((E/'s1-claims-nuc-extract-run10/llbc-info.json').read_text())['has_errors'] is False
successful={'s1-claims-unrolled-types-v2':'S1ClaimsUnrolledTypesV1','s1-claims-unrolled-helpers-v1':'S1ClaimsUnrolledHelpersV1','s1-claims-source-reads-v2':'S1ClaimsSourceReadsV1','s1-claims-unrolled-parent-v1':'S1ClaimsUnrolledParentV1','s1-claims-unrolled-accepted-v1':'S1ClaimsUnrolledAcceptedV1'}
for attempt,module in successful.items():
 d=E/attempt;j=json.loads((d/'receipt.json').read_text())
 assert j['exit_status']==0 and j['swaps']==0 and j['target']==module
 assert sha(S/(module+'.lean'))==j['source_sha256']==sha(d/'source.lean')
 assert j['print_axioms'] and all('sorryAx' not in x for x in j['print_axioms'])
 for line in j['print_axioms']:
  if 'depends on axioms:' in line:
   assert set(re.search(r'\[(.*)\]',line)[1].split(', '))<={'propext','Classical.choice','Quot.sound'}
 source=(S/(module+'.lean')).read_text()
 assert not re.search(r'(?m)^\s*(axiom|set_option (maxHeartbeats|maxRecDepth))\b|\b(sorry|native_decide|bv_decide)\b',source)
 assert '_Template' not in source and 'TypesExternal' not in source and 'FunsExternal' not in source
# Reconstruct exact complete emitted helper/parent chunks and permitted changes.
raw=E/'s1-claims-nuc-extract-run10/generated/AspisS1ClaimsUnrolledSource/Funs.lean';s=raw.read_text();defs=list(re.finditer(r'(?m)^def\s+([A-Za-z0-9_.]+)',s));chunks={}
for i,d in enumerate(defs):
 start=s.rfind('/--',0,d.start());end=s.rfind('/--',0,defs[i+1].start())if i+1<len(defs)else s.index('\nend AspisS1ClaimsUnrolledSource',d.end());chunks[d[1]]=s[start:end]
for kind,module in [('helpers','S1ClaimsUnrolledHelpersV1'),('parent','S1ClaimsUnrolledParentV1')]:
 bind=json.loads((R/f'tools/s1-claims-unrolled-20261025/{kind}-binding.json').read_text());maint=(S/(module+'.lean')).read_text()
 assert bind['raw_sha256']==sha(raw) and bind['maintained_sha256']==sha(S/(module+'.lean'))
 for row in bind['complete_declarations']:
  chunk=chunks[row['name']]
  if kind=='helpers':assert hashlib.sha256(chunk.encode()).hexdigest()==row['sha256'] and chunk in maint
  else:
   assert hashlib.sha256(chunk.encode()).hexdigest()==row['raw_sha256']
   if row['name'].endswith('filled'):chunk=chunk.replace('{T : Type} (coremarkerCopyInst','{T : Type} (backend : PrimitivePorts) (coremarkerCopyInst')
   else:chunk=chunk.replace('(prefix1 : r1_wire.Prefix)','(backend : PrimitivePorts) (prefix1 : r1_wire.Prefix)')
   for a,b in [('alloc.vec.Vec.try_reserve_exact','backend.reserve'),('alloc.vec.Vec.into_boxed_slice','backend.intoBox'),('BoxArray.Insts.CoreConvertTryFromBoxSliceBoxSlice.try_from','backend.toArray'),('r1_wire.ValidatedRecord.decode_k','backend.decode')]:chunk=chunk.replace(a,b)
   if row['name']=='candidate_claims.claims':chunk=chunk.replace('aspis_core.r0.heap.filled (','aspis_core.r0.heap.filled backend (')
   assert hashlib.sha256(chunk.encode()).hexdigest()==row['parameterized_sha256'] and chunk in maint
b=json.loads((R/'tools/s1-claims-unrolled-20261025/types-binding.json').read_text());assert b['raw_sha256']==sha(raw.with_name('Types.lean')) and b['maintained_sha256']==sha(S/'S1ClaimsUnrolledTypesV1.lean')
# Native unroll result is under explicit normal-return decoder/allocator cuts.
d=E/'s1-claims-unrolled-v2';j=json.loads((d/'receipt.json').read_text());assert j['exit_status']==0 and j['swaps']==0 and j['watchdog_stop'] is None
assert all(j['source_unchanged'].values()) and all(j['tools_unchanged'].values())
for name,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(d/name)==j[key]
log=(d/'stdout.log').read_text();assert '0 of 1029 failed' in log and '4 of 4 cover properties satisfied' in log
print(f'PASS {len(m["files"])} source/evidence pins; TOTAL getter and ACCEPTED-ONLY four-port parent proved. Concrete primitive/native SDK/source-release joins OPEN; S1/S6 and 100-bit target NOT established.')
