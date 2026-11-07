"""Validate local receipts/artifact archives; no proof rebuild or host mutation."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess
P=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(l) for l in (P/'NNC_ATTEMPTS.jsonl').read_text().splitlines()]
scopes=[r for r in rows if r.get('full_receipt')]
assert len(scopes)<=250
archives=0
for p in P.rglob('*.sha256'):
 z=p.with_suffix(p.suffix.removesuffix('sha256')+'xz')
 if not z.exists():continue
 assert sha(lzma.decompress(z.read_bytes()))==p.read_text().split()[0],str(p)
 archives+=1
for p in (P/'NNC_INPUTS').glob('*.xz'):
 assert sha(lzma.decompress(p.read_bytes()))==p.stem,p
inputs=json.loads((P/'NNC_INPUTS.json').read_text())
for h,x in inputs['objects'].items():
 p=P/x['path'];assert sha(p.read_bytes())==x['archive_sha256']
 raw=lzma.decompress(p.read_bytes());assert sha(raw)==h and len(raw)==x['bytes']
axioms=[];modules=[]
for p in P.glob('*.lean'):
 if p.stem.endswith('Driver'):continue
 matches=[r for r in scopes if r.get('module')==p.stem and r['exit_status']==0 and sha(p.read_bytes()) in r['source_hashes'].values()]
 assert matches,'Unvalidated current module '+p.stem
 modules.append(dict(module=p.stem,attempt=matches[-1]['attempt'],sha256=sha(p.read_bytes())))
 for line in matches[-1].get('print_axioms',[]):
  assert 'sorryAx' not in line,line
  axioms.append(line)
for r in scopes:
 p=P/r['full_receipt'];assert sha(p.read_bytes())==r['full_receipt_sha256']
 full=json.loads(p.read_text());assert full['exit_status']==r['exit_status']
 ad=json.loads((P/(r['attempt']+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert full['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},full['limits']
 for n,h in full['source_hashes'].items():
  assert h in inputs['attempts'][r['attempt']].values() or n==r['attempt']+'.json',(r['attempt'],n)
standard={'propext','Classical.choice','Quot.sound'}
roots=json.loads((P/'NNC_AUDIT_ROOTS.json').read_text())['roots']
results=[]
for p in sorted((P/'NNC_audit').glob('batch*/proof*.json')):
 x=json.loads(p.read_text());assert x['exit_status']==0,p
 results+=x['results']
assert sorted(r['root'] for r in results)==sorted(roots)
for r in results:assert set(r['walked_axioms'])<=standard,r
large=[str(p) for p in P.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
assert not large,large
changed=subprocess.check_output(['git','diff','--name-only','cfa73190568','--'],text=True).splitlines()
assert all(x.startswith('evidence/root0-weak-20261111/') for x in changed),changed
report=dict(status='PASS',security_target='NOT_ESTABLISHED',scope_count=len(scopes),budget=250,kani=0,extraction=0,
 scope_wall_seconds=sum(r['wall_seconds'] for r in scopes),peak_rss_kib=max(int(r['peak_rss_kib']) for r in scopes),swaps=sum(int(r['swaps']) for r in scopes),
 failed_scopes=[r['attempt'] for r in scopes if r['exit_status']!=0],archive_sha_pairs=archives,input_archives=len(list((P/'NNC_INPUTS').glob('*.xz'))),
 current_modules=modules,raw_audited_roots=len(results),raw_axioms=sorted(set(a for r in results for a in r['walked_axioms'])),collector_disagreements=[r for r in results if not r['equal']],
 files_over20MB=large,shipped_changes=[],trust_changes=[],actual_tas_instance='OPEN',print_axioms=axioms)
(P/'NNC_VALIDATION.json').write_text(json.dumps(report,indent=1)+'\n')
(P/'NNC_AUDIT.json').write_text(json.dumps(dict(status='PASS',scope=str(len(results))+' own roots only',roots=results,collector_disagreements=report['collector_disagreements']),indent=1)+'\n')
print(json.dumps({k:report[k] for k in ['status','scope_count','raw_audited_roots','peak_rss_kib','swaps','archive_sha_pairs','collector_disagreements']}))
