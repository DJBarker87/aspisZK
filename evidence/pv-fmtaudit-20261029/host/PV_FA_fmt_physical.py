from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029');C=json.loads((H/'cohorts.json').read_text());out=[]
for k,paths in C.items():
 for i,root in enumerate(paths.split(':')):
  p=Path(root)/'Aeneas/Std/Core/Fmt.olean'
  if p.exists():
   out.append(dict(cohort=k,path=str(p),root_index=i,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,companions=[dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size)for q in p.parent.glob('Fmt.olean.*')]))
(H/'fmt-physical-objects.json').write_text(json.dumps(out,indent=1));print(json.dumps(out,indent=1))
M=json.loads((H/'resolution.json').read_text());order=json.loads((H/'pin-rebuild-order.json').read_text());fresh={m.replace('.','/')for m in order};pairs=[]
for r in M:
 if r['cohort']not in ['authority','ndr']or not r['module'].startswith(('Aeneas/','AeneasMeta/'))and r['module']not in ['Aeneas','AeneasMeta']:continue
 mod=r['module'];left=H/'pinned-objects'/(mod+'.olean')
 if left.exists()and r['sha256']:
  pairs.append('\t'.join([r['cohort']+('-fresh-source'if mod in fresh else'-reused-baseline'),mod,str(left),r['path']]))
for r in out:pairs.append('\t'.join(['physical-fmt', 'Aeneas/Std/Core/Fmt',str(H/'pinned-objects/Aeneas/Std/Core/Fmt.olean'),r['path']]))
(H/'object-pairs.tsv').write_text('\n'.join(pairs)+'\n')
