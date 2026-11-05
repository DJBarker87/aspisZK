"""Self-excluding evidence inventory and retained compressed-walk validation."""
from pathlib import Path
import json,hashlib,lzma,subprocess,sys
E=Path(__file__).resolve().parent;R=E.parents[1];out=E/'NHN_FILES.json'
H=lambda b:hashlib.sha256(b).hexdigest()
for p in E.rglob('*'):
 assert p.name!='__pycache__'
 if p.is_file():assert p.stat().st_size<=20_000_000,p
for p in E.glob('*REACHABLE.txt.xz'):
 raw=lzma.decompress(p.read_bytes());want=Path(str(p)[:-3]+'.sha256').read_text().split()[0];assert H(raw)==want,p
names=subprocess.check_output(['git','diff','--name-only','98beca70777'],cwd=R,text=True).splitlines()
assert all(n.startswith('evidence/q-leftovers-20261106/')for n in names),names
files={str(p.relative_to(E)):{'sha256':H(p.read_bytes()),'bytes':p.stat().st_size}for p in sorted(E.rglob('*'))if p.is_file()and p!=out}
if '--check'in sys.argv:assert json.loads(out.read_text())['files']==files
else:out.write_text(json.dumps(dict(files=files,self_excluded=out.name,all_files_under_20MB=True,source_scope='own evidence directory only',shipped_changes=[],frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'),indent=1)+'\n')
print(json.dumps(dict(status='PASS',files=len(files),total_bytes=sum(v['bytes']for v in files.values()),compressed_raw_walks=len(list(E.glob('*REACHABLE.txt.xz'))))))
