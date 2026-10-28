from pathlib import Path
import json,hashlib
R=Path('/home/dombarker/project-offloads/codex-pv-kscan-20261028');P=R.parent
want=json.loads((R/'d347-input.json').read_text())['passes']; names={p['harness'] for p in want}; rows=[]
for line in (R/'metadata-paths-d347.txt').read_text().splitlines():
 p=Path(line)
 try:j=json.loads(p.read_text())
 except (ValueError,OSError):continue
 for h in j.get('proof_harnesses',[]):
  if h['pretty_name'] not in names:continue
  f=Path(h['goto_file']); f=f.with_name(f.name.replace('.symtab.out','.out'))
  if not f.exists():continue
  rows.append(dict(metadata_path=str(p),metadata_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),harness=h,goto=str(f),goto_size=f.stat().st_size))
(R/'d347-discovery.json').write_text(json.dumps(rows,indent=2)+'\n')
print('metadata matches',len(rows),'distinct',len({r['harness']['pretty_name'] for r in rows}))
for n in sorted(names):
 matches=[r for r in rows if r['harness']['pretty_name']==n]
 print(n, len(matches), [r['goto'] for r in matches][:2])
