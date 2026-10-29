"""Stage verified unaffected cache files at the explicitly authorized original prefix."""
from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2g-20261029');p=json.loads((D/'plan.json').read_text());pre=json.loads((D/'preflight.json').read_text());O=Path(p['environment']['LEAN_PATH'].split(':')[0]);assert str(O)=='/home/dombarker/project-offloads/codex-pv-rdb2e-20261029/lean-objects';assert not O.exists();O.mkdir()
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
rows=[];lookup={r['module']:r for r in p['objects']}
for r in pre['objects']:
 if r['module'] in p['build_order']:continue
 q=Path(r['matches'][0]['path']);assert sha(q)==r['expected_object_sha256'];out=O/(r['module'].replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,out)
 cs=[]
 for src,dst in [(Path(str(q)+'.server'),Path(str(out)+'.server')),(Path(str(q)+'.private'),Path(str(out)+'.private')),(q.with_suffix('.ir'),out.with_suffix('.ir'))]:
  if src.exists():
   h=sha(src);expected=[x['sha256'] for x in lookup[r['module']]['companions'] if x['path'].endswith('.'+('ir' if src.suffix=='.ir' else src.suffix[1:]))]
   if expected:assert h in expected,(src,h,expected)
   shutil.copyfile(src,dst);cs.append(dict(source=str(src),path=str(dst),sha256=h))
 rows.append(dict(module=r['module'],source=str(q),path=str(out),sha256=sha(out),companions=cs))
(D/'env-J.json').write_text(json.dumps(p['environment'],indent=2));(D/'staged.json').write_text(json.dumps(rows,indent=2));print('Staged',len(rows),'unaffected canonical objects and companions; zero affected objects reused')
