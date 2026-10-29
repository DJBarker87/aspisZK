from pathlib import Path
import json
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029');rows=json.loads((H/'claim-object-locations.json').read_text());aud={r['id']:r for r in json.loads((H/'claim-audit-dispositions.json').read_text())};lines=[];records=[]
for r in rows:
 candidates=[]
 target=str((aud[r['id']].get('selected_standard_audit')or{}).get('receipt_status',[]))
 for o in r['objects']:
  root=Path(o['root']);job=root.parent
  for name in ['env-J-private.json','env-J.json','J.json','env/J.json']:
   p=job/name
   if not p.exists():continue
   e=json.loads(p.read_text());lp=e.get('LEAN_PATH')
   if not lp:continue
   roots=[str(root)]+lp.split(':');candidates.append((str(root)in target,dict(**o,env=str(p),roots=list(dict.fromkeys(roots)))))
   break
 candidates.sort(key=lambda x:x[0],reverse=True)
 if candidates:
  o=candidates[0][1];lines.append('\t'.join([r['id'],r['theorem'],':'.join(o['roots'])]));records.append(dict(id=r['id'],selected=o,other_objects=r['objects']))
 else:records.append(dict(id=r['id'],selected=None,other_objects=r['objects']))
(H/'footprint-inputs.tsv').write_text('\n'.join(lines)+'\n');(H/'footprint-source-resolution.json').write_text(json.dumps(records,indent=1));print('prepared',len(lines),'gaps',[r['id']for r in records if r['selected']is None])
