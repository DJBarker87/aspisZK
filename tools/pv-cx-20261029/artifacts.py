"""Record raw extractor verdicts, source byte checks, and compressed text archives."""
from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029');rows=[]
for o in sorted(H.glob('N733[0-2][0-9]')):
 p=o/'PV_CX_Entry.llbc'
 if not p.exists():continue
 raw=p.read_bytes();d=json.loads(raw);t=d['translated'];inputs=json.loads((o/'command.json').read_text())['input_sha256'];sources=[]
 for f in t['files']:
  n=f.get('name',{}).get('Local');content=f.get('contents')
  if not n or content is None:continue
  if n.startswith(str(H/'src')+'/'):rel=n[len(str(H/'src'))+1:]
  elif n.startswith('src/bin/'):rel='tools/r1-cost-probe/'+n
  else:continue
  h=hashlib.sha256(content.encode()).hexdigest();sources.append(dict(path=rel,sha256=h,matches_input=h==inputs.get(rel)))
 assert all(s['matches_input'] for s in sources),sources
 row=dict(attempt=o.name,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),has_errors=d['has_errors'],charon_version=d['charon_version'],options=t['options'],embedded_project_sources=sources)
 (o/'llbc-status.json').write_text(json.dumps(row,indent=2)+'\n');rows.append(row)
 for a in (H/'archives').glob(o.name+'.llbc.xz'):
  (H/'archives'/(o.name+'.llbc.sha256')).write_text(row['sha256']+'  '+o.name+'.llbc\n')
  row['archive']=dict(path=str(a),bytes=a.stat().st_size,sha256=hashlib.sha256(a.read_bytes()).hexdigest())
(H/'artifact-manifest.json').write_text(json.dumps(rows,indent=2)+'\n');print([(r['attempt'],r['has_errors']) for r in rows])
