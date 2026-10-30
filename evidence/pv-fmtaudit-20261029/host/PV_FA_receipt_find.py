from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029');rows=json.loads((H/'claim-recorded-object-paths.json').read_text());prior=json.loads((H/'formatter-footprints.json').read_text());done={r['id']for r in prior if not r['import_gaps']and not r['unresolved_project_constants']};out=[];lines=[]
for r in rows:
 if r['id']in done or not r['theorem']:continue
 rel=r['theorem'].rsplit('.',1)[0].replace('.','/')+'.olean';options=[]
 for rec in r['records']:
  for x in rec['paths']:
   p=Path(x['path'])
   if not p.exists():continue
   h=hashlib.sha256(p.read_bytes()).hexdigest()
   if x.get('sha256')and x['sha256']!=h:continue
   for ep in rec['envs']:
    e=Path(ep)
    if not e.exists():continue
    env=json.loads(e.read_text());lp=env.get('LEAN_PATH')
    if not lp:continue
    root=str(p)[:-len(rel)].rstrip('/');options.append(dict(path=str(p),sha256=h,matches_recorded_sha=bool(x.get('sha256')),env=ep,roots=list(dict.fromkeys([root]+lp.split(':'))),receipt=rec['receipt']))
 options.sort(key=lambda x:x['matches_recorded_sha'],reverse=True);s=options[0]if options else None;out.append(dict(id=r['id'],selected=s,options=options))
 if s:lines.append('\t'.join([r['id'],r['theorem'],':'.join(s['roots'])]))
(H/'receipt-recovered-objects.json').write_text(json.dumps(out,indent=1));(H/'footprint-inputs-more.tsv').write_text('\n'.join(lines)+'\n');print('recovered',[(x['id'],x['selected']['matches_recorded_sha'])for x in out if x['selected']]);print('missing',[x['id']for x in out if not x['selected']])
