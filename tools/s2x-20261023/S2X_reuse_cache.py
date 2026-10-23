"""Copy missing existing proof cache objects into this worker's private host dir.
No compilation and no writes to another worktree or shared object directory.
"""
from pathlib import Path
import json,hashlib,subprocess,shlex
R=Path(__file__).resolve().parents[2]; D=R/'docs/research/100bit-spend-path-20261013'; E=D/'evidence/s2x-20261023'
H='/home/dombarker/project-offloads/codex-cx-s2x-20261023'; HOST='dombarker@100.108.41.90'
cfg=json.loads((R/'tools/s2x-20261023/lean-004.json').read_text())
old=json.loads((D/'evidence/stored-carrier-20261021/StoredCarrierRawLayout-2/command.json').read_text());paths=old['lean_path'].split(':')
seen={}
def visit(module):
 if module in seen:return
 p=D/'lean'/(module.replace('.','/')+'.lean')
 if not p.is_file():return
 seen[module]=p
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for m in line[7:].split():visit(m)
visit('R9PoolRuntimeBinding')
script='import json,sys,pathlib; x=json.load(sys.stdin); print(json.dumps([m for m in x["modules"] if not any((pathlib.Path(r)/(m.replace(".","/")+".olean")).is_file() for r in x["roots"])]))'
missing=json.loads(subprocess.check_output(['ssh',HOST,'python3 -c '+shlex.quote(script)],input=json.dumps(dict(modules=list(seen),roots=cfg['env']['LEAN_PATH'].split(':'))),text=True))
subprocess.run(['ssh',HOST,'mkdir -p '+H+'/reused-objects'],check=True)
rows=[]; unavailable=[]
print("Missing source-graph candidates:",missing,flush=True)
for m in missing:
 key=m.replace('.','/')+'.olean'; p=next((Path(r)/key for r in paths if r and (Path(r)/key).is_file()),None)
 if p is None:
  unavailable.append(m); continue
 src=seen[m]; row=dict(module=m,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),objects=[])
 # Only top-level soundness modules are missing here.
 assert '/' not in key,key
 for q in [p,Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')]:
  if not q.is_file():continue
  row['objects'].append(dict(local_path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
  subprocess.run(['scp',str(q),HOST+':'+H+'/reused-objects/'+q.name],check=True)
 rows.append(row)
 (E/'reused-cache.json').write_text(json.dumps(dict(scope='existing objects reused; not a coherent dependency rebuild',provenance='local object roots from StoredCarrierRawLayout-2 command; R9 top object matches its receipt pin',copied=rows,unavailable_source_graph_candidates=unavailable),indent=2)+'\n')
(E/'reused-cache.json').write_text(json.dumps(dict(scope='existing objects reused; not a coherent dependency rebuild',provenance='local object roots from StoredCarrierRawLayout-2 command; R9 top object matches its receipt pin',copied=rows,unavailable_source_graph_candidates=unavailable),indent=2)+'\n')
print('Copied existing modules:',[r['module'] for r in rows]);print('Unavailable source-graph candidates (may differ from actual cached imports):',unavailable)
