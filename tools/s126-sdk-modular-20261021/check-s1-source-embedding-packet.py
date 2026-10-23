#!/usr/bin/env python3
"""Audit actual embedding installation and full query Result law; no replay."""
from pathlib import Path
import json,hashlib,re,subprocess,tempfile
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=E/'s1-m31-embedding';load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(P/'manifest.json');assert {str(p.relative_to(P)) for p in P.rglob('*') if p.is_file()}==set(m['files'])|{'manifest.json'}
for rel,d in m['files'].items():assert sha(P/rel)==d,rel
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc','.pyc','.exe'] for p in P.rglob('*'))
for v in [1,2]:
 llbc=load(P/'embedding'/f'v{v}'/'Embedding.llbc.json');assert not llbc['has_errors']
 for phase in ['charon','aeneas']:
  tag=f's1-m31-embedding-{phase}-v{v}';r=load(P/'receipts'/tag/'receipt.json');assert r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0'
  i=load(P/(tag+'-input.json'));assert i['entry_sha256']==sha(P/'embedding'/f'v{v}'/'src/lib.rs')
  for rel,d in i['dependency_source_pins'].items():assert sha(P/'dependency/aspis-core'/rel)==d
f=(P/'embedding/v2/generated/AspisS1M31Embedding/Funs.lean.txt').read_text();t=(P/'embedding/v2/generated/AspisS1M31Embedding/Types.lean.txt').read_text();assert 'FunsExternal' not in f and 'TypesExternal' not in t
assert f.count('def aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31')==1
assert 'def aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31' in f and 'def aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31' in f
assert 'aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31' in f
with tempfile.TemporaryDirectory() as d:
 raw=Path(d)/'raw';out=Path(d)/'out';raw.mkdir()
 for name,content in [('Types.lean',t),('Funs.lean',f)]:(raw/name).write_text(content)
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/adapt-s1-m31-embedding.py'),str(raw),str(out)],check=True)
 for name in ['S1M31EmbeddingSourceV1.lean','s1-m31-embedding-adapter.json']:assert (out/name).read_bytes()==(S/name).read_bytes()
rows=[('S1M31EmbeddingSourceV1','s1-m31-embedding-source-v1'),('S1M31EmbeddingTotalV1','s1-m31-embedding-total-v2'),('S1QueryTraceEmbeddingV1','s1-query-trace-embedding-v3'),('S1OriginalPreparedSourceEmbeddingV1','s1-original-prepared-source-embedding-v1')];accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s1-source-embedding-import-pins.json');reports=0
for name,attempt in rows:
 r=load(E/attempt/'receipt.json');c=load(E/attempt/'command.json');assert r['exit_status']==0 and r['swaps']==0
 assert sha(S/(name+'.lean'))==sha(E/attempt/'source.lean')==r['source_sha256']==pins['targets'][name]['source_sha256']==accepted[name]['source_sha256']
 assert r['object_sha256']==pins['targets'][name]['object_sha256'] and '-j1' in c['command'] and '-M4400' in c['command']
 src=(S/(name+'.lean')).read_text();assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',src,re.M)
 for report in r['print_axioms']:
  x=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert x and set(re.findall(r'[A-Za-z_.]+',x[1]))<={'propext','Classical.choice','Quot.sound'};reports+=1
assert reports==11
for rel,hashes in load(E/'s1-m31-embedding-source-overlay.json')['files'].items():
 assert len(set(hashes.values()))==1
 for rev,d in hashes.items():assert hashlib.sha256(subprocess.check_output(['git','-C',str(R),'show',rev+':'+rel])).hexdigest()==d
q=(S/'S1QueryTraceEmbeddingV1.lean').read_text();assert q.count('let we')==22
sig=q[q.index('theorem queries_actual_embed'):q.index(' := by',q.index('theorem queries_actual_embed'))];assert '(h' not in sig and '{B with embed:=actualEmbed}' in sig
for tag in ['s1-original-claim-joinfix-v1','s1-original-claim-collapse-v1']:
 r=load(P/'receipts'/tag/'receipt.json');assert r['exit_status']!=0 and r['swaps']==0
build=load(P/'tool-build/v3/receipt.json');assert build['exit_status']==0 and build['process_swaps']==0 and build['swap_bytes']==0
assert build['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert 'Returns inside of nested loops' in (P/'receipts/s1-original-claim-joinfix-v1/stderr.log').read_text()
assert 'option is None' in (P/'receipts/s1-original-claim-collapse-v1/stderr.log').read_text()
print(json.dumps(dict(accepted_targets=4,standard_axiom_reports=reports,embedding_total=True,query_trace_result_identity=True,original_claim_translation_closed=False,whole_s1_closed=False,whole_s6_closed=False)))
