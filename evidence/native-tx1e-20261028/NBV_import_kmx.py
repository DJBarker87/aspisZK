from pathlib import Path
import sys,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBV_host as h
expected=json.loads((R/'evidence/kani-mitig-20261028/KMX_CLEANUP.json').read_text())['objects']['cache']['objects']
source=R/'lean/KMX_CopyMeaning.lean';assert hashlib.sha256(source.read_bytes()).hexdigest()=='2baec49a3446a3bbb2be6f992c97d0a6897534a1cd308db8746194dedf665f2b'
h.admit('NBV_KMXIMPORT')
r=h.remote_py(f'''from pathlib import Path
import shutil,json,hashlib
out={{}}
for name,info in {expected!r}.items():
 p=Path(name);assert hashlib.sha256(p.read_bytes()).hexdigest()==info['sha256']
 q=Path({h.CACHE!r})/p.name;assert not q.exists();shutil.copyfile(p,q)
 out[str(q)]=dict(source=name,sha256=hashlib.sha256(q.read_bytes()).hexdigest(),size=q.stat().st_size)
print(json.dumps(out))''');assert r.returncode==0,r.stderr
(E/'NBV_KMX_IMPORTED_PINS.json').write_text(r.stdout)
