"""Read-only recovery of already-passed header raw-walk artifacts. No replay."""
from pathlib import Path
import json,subprocess,lzma,hashlib,datetime
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106'
code="from pathlib import Path\nimport json\nb=Path("+repr(B)+")\nprint(json.dumps({p.name:p.read_text() for p in b.glob('NEP_proof1_*_REACHABLE.txt')}))\n"
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);rows=[]
for n,t in out.items():
 b=t.encode();h=hashlib.sha256(b).hexdigest();z=E/(n+'.xz')
 if z.exists():assert lzma.decompress(z.read_bytes())==b
 else:z.write_bytes(lzma.compress(b))
 (E/(n+'.sha256')).write_text(h+'  '+n+'\n');rows.append(dict(path=n,sha256=h,bytes=len(b)))
assert len(rows)==3
(E/'NHY_RAW_RECOVERY.json').write_text(json.dumps(dict(source='NHY_L011 already-passed proof1',mode='read-only ssh, no submission/replay',host_directory=B,recovered_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),rows=rows),indent=1)+'\n');print('recovered',len(rows),'raw artifacts')
