"""Verify retained own exports/seeds, then remove only rebuildable own outputs."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
assert json.loads((E/'NKC_VALIDATION.json').read_text())['status']=='PASS'
code='''from pathlib import Path
import json,hashlib,shutil,lzma
B=Path('/home/dombarker/project-offloads/codex-cx-ledger17-20261108')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((B/'NKC_EXPORT.json').read_text())
for r in x['files']:assert H(Path(r['path']))==r['sha256']
seed=json.loads(lzma.decompress((B/'NKC_CACHE_IMPORTS.json.xz').read_bytes()))
for r in seed['files']:assert H(Path(r['destination']))==r['sha256']
paths=[B/n for n in ['NKC_objects','NKC_native','NKC_tmp','NKC_target']]
paths += list(B.glob('NEP_*_REACHABLE.txt'))
removed=[]
for p in paths:
 assert p.parent==B and p.name.startswith(('NKC_','NEP_'))
 if not p.exists():continue
 size=sum(q.stat().st_size for q in p.rglob('*')if q.is_file())if p.is_dir()else p.stat().st_size
 removed.append(dict(path=str(p),bytes=size))
 if p.is_dir():shutil.rmtree(p)
 else:p.unlink()
out=dict(status='PASS_OWN_OUTPUT_CLEANUP',verified_export_files=len(x['files']),verified_seed_files=len(seed['files']),removed=removed,removed_bytes=sum(r['bytes']for r in removed),retained_cache=x['export'],no_shared_cache_or_key_touched=True,disk=shutil.disk_usage(B)._asdict())
(B/'NKC_HOST_END.json').write_text(json.dumps(out,indent=1)+'\\n')
print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
# A lost connection after submission requires read-only recovery, never deletion resubmission.
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NKC_HOST_END.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(status=x['status'],removed_bytes=x['removed_bytes'],export_files=x['verified_export_files'])))
