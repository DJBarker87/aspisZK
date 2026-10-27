"""Read-only final pin check: private project outputs and loaded external artifacts."""
from pathlib import Path
import hashlib,json,re,time
P=Path('/home/dombarker/project-offloads/codex-pv-replay-20261027');E=P/'evidence';O=P/'objects'
plan=json.loads((P/'replay-plan.json').read_text()); results={r['module']:r for r in map(json.loads,(E/'results.jsonl').read_text().splitlines())}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(2**20):h.update(b)
 return h.hexdigest()
rows=[];bad=[]
for m,n in plan['nodes'].items():
 s=P/'sources'/(m+'.lean');o=O/(m+'.olean');r=results[m]
 row=dict(module=m,source_sha256=sha(s),expected_source_sha256=n['source_sha256'],status=r['status'],object_sha256=sha(o) if o.is_file() else None,expected_object_sha256=r.get('object_sha256'))
 if row['source_sha256']!=row['expected_source_sha256'] or row['object_sha256']!=row['expected_object_sha256']:bad.append(row)
 rows.append(row)
for d in json.loads((E/'external-boundary.json').read_text()):
 q=O/(d['module']+'.olean');h=sha(q)
 if h!=d['sha256']:bad.append(dict(module=d['module'],external_boundary_expected=d['sha256'],actual=h))
external=[]
if (E/'audit-result.json').exists():
 a=json.loads((E/'audit-result.json').read_text());text=(E/f"out-{a['attempt']}.log").read_text()
 for z in re.finditer(r'PV_REPLAY_IMPORT (\S+) :',text):
  m=z[1].replace('.','/')
  if m in plan['nodes']:continue
  q=O/(m+'.olean')
  if not q.is_file():bad.append(dict(module=m,reason='loaded external object absent from private mirror'));continue
  external.append(dict(module=m,path=str(q.resolve()),object_sha256=sha(q),object_bytes=q.stat().st_size))
large=[]
for name in ['external-loader-files.json']:
 q=E/name
 if q.exists():large.append(dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size,reason='retained on host; hash+size committed instead of full redundant namespace-binding listing'))
r=dict(revision=plan['revision'],project_modules_checked=len(rows),external_boundary_checked=len(json.loads((E/'external-boundary.json').read_text())),project_results=rows,mismatches=bad,all_pass=not bad,retained_host_artifacts=large)
(E/'final-integrity.json').write_text(json.dumps(r,indent=2)+'\n');(E/'external-object-manifest.json').write_text(json.dumps(external,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['revision','project_modules_checked','external_boundary_checked','all_pass','mismatches']}));print('loaded external modules',len(external))
