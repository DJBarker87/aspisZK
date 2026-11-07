"""Copy only one missing module namespace from the pinned ordered roots."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;ns=sys.argv[1];assert ns.replace('_','').isalnum()
code='''from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-integrate-20261111');out=b/'NNH_seed';seen=set();rows=[]
assert shutil.disk_usage(b).free>=40_000_000_000
for root in paths:
 p=Path(root)/ns
 if not p.is_dir():continue
 for src in sorted(p.rglob('*')):
  if not src.is_file() or not any(str(src).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
  rel=ns+'/'+str(src.relative_to(p))
  if rel in seen:continue
  seen.add(rel);dst=out/rel;dst.parent.mkdir(parents=True,exist_ok=True);h=hashlib.sha256(src.read_bytes()).hexdigest()
  if not dst.exists():shutil.copy2(src,dst)
  assert hashlib.sha256(dst.read_bytes()).hexdigest()==h,str(dst)
  rows.append(dict(path=str(src),destination=str(dst),sha256=h,bytes=dst.stat().st_size))
assert rows,ns
print(json.dumps(rows))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='ns='+repr(ns)+'\npaths='+repr(json.loads((E/'NNH_SEED_PATHS.json').read_text()))+'\n'+code,text=True,capture_output=True)
(E/('NNH_SEED_'+ns+'.json')).write_text(r.stdout);assert r.returncode==0,r.stderr
print('Copied',len(json.loads(r.stdout)),'namespace objects')
