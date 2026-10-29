"""Read-only final input/source/dependency and admission audit."""
from pathlib import Path
import json,hashlib,re,sys
D=Path('/home/dombarker/project-offloads/codex-pv-diag3-20261029');mode=sys.argv[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bad=[];latest={};receipts=[]
for p in sorted(D.glob('*-receipt.json')):
 r=json.loads(p.read_text());receipts.append((p,r))
 if r.get('module') and r['exit']==0:latest[r['module']]=r
 if r.get('admission_exit')!=0 or r.get('admission_allowed') is not True:bad.append(dict(receipt=str(p),reason='invalid admission'))
for m,r in latest.items():
 src=D/'sources'/(m.replace('.','/')+'.lean');obj=D/'objects'/(m.replace('.','/')+'.olean')
 if sha(src)!=r['source_sha256'] or sha(obj)!=r['object_sha256']:bad.append(dict(module=m,reason='source/object changed after accepted compile'))
 for dep,files in r['dependency_objects'].items():
  for file,expected in files.items():
   if sha(Path(file))!=expected:bad.append(dict(module=m,dependency=dep,path=file,reason='dependency changed'))
 text=src.read_text()
 if re.search(r'\b(?:sorry|admit|native_decide|implemented_by)\b|^\s*axiom\b|^\s*import XR|set_option (?:maxRecDepth|maxHeartbeats)',text,re.M):bad.append(dict(module=m,reason='forbidden source'))
 for th in re.findall(r'^theorem (\w+)',text,re.M):
  if '#print axioms '+th not in text:bad.append(dict(module=m,theorem=th,reason='missing explicit axioms print'))
 for ax in re.findall(r'depends on axioms:\s*\[([^]]*)\]',r['print_axioms']):
  if not set(x.strip() for x in ax.split(','))<={'propext','Classical.choice','Quot.sound'}:bad.append(dict(module=m,axioms=ax))
cache=json.loads((D/'retry-cache-preflight.json').read_text());assert not cache['mismatches']
for m,r in cache['rows'].items():
 if sha(Path(r['path']))!=r['sha256']:bad.append(dict(module=m,reason='h6 object changed'))
for r in json.loads((D/'external-authority.json').read_text()):
 if sha(Path(r['path']))!=r['object_sha256']:bad.append(dict(module=r['module'],reason='external object changed'))
for r in json.loads((D/'sidecar-pins.json').read_text()):
 if sha(Path(r['path']))!=r['sha256']:bad.append(dict(path=r['path'],reason='sidecar changed'))
# Exact launch intervals prevent hidden overlap of this job's capped scopes.
intervals=sorted((r.get('started_epoch',p.stat().st_mtime-r['wall_seconds']),p.stat().st_mtime,p.name) for p,r in receipts)
for a,b in zip(intervals,intervals[1:]):
 if a[1]>b[0]+0.01:bad.append(dict(reason='scope interval overlap',first=a,second=b))
if mode=='post':
 for n in [64197,64198,64199]:assert json.loads((D/f'lean{n}-receipt.json').read_text())['exit']==0
result=dict(mode=mode,latest_modules=latest,checked_cache=cache['checked'],external_objects=5673,scope_intervals=intervals,mismatches=bad,whole_privacy_release_replay=False,source_revision=(D/'revision.txt').read_text().strip())
(D/f'final-{mode}.json').write_text(json.dumps(result,indent=2)+'\n')
print(mode,'accepted modules',len(latest),'scopes',len(receipts),'mismatches',len(bad));print(json.dumps(bad[:5],indent=2));assert not bad
