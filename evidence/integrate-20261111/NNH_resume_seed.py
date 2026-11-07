"""Bounded copy of committed library manifests; never traverse caches."""
from pathlib import Path
import json,lzma,subprocess,hashlib
E=Path(__file__).resolve().parent
rows=[]
x=json.load(open('evidence/lib-20261111/LIB_BUNDLE_EXPORT.json'));rows+=x['files']
x=json.load(open('evidence/libb-20261111/LIBB_EXPORT.json'));rows+=x['objects']
x=json.load(open('evidence/libc-20261111/LIBC_EXPORT.json'));rows+=x['files']
x=json.loads(lzma.open('evidence/lib-20261111/LIB_BUNDLE_CLOSURE_PINS.json.xz').read());rows+=x['selected_modules']
# Gate additions have committed focused receipts, rather than the older export.
for p in sorted(Path('evidence/libb-20261111').glob('LIBB_L*/receipt.json')):
 x=json.load(open(p))
 for path,pin in x.get('deps_fingerprint',{}).get('selected_objects',{}).items():
  if Path(path).name.startswith('LIBB_'): rows.append(dict(path=path,sha256=pin['sha256']))
for mod in ['LIBB_V2Star','LIBB_Tx2AuthGate','LIBB_ReturnFunctional','LIBB_ReturnTrace','LIBB_ReturnRun','LIBB_ReturnObservation']:
 # New roots are compiled privately from committed sources below.
 pass
code='''from pathlib import Path
import json,shutil,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-integrate-20261111');dst=b/'NNH_library_seed';dst.mkdir(exist_ok=True)
assert shutil.disk_usage(b).free>=40_000_000_000
out=[];seen=set()
for row in rows:
 p=Path(row['path']);rel=p.name
 if rel in seen:continue
 seen.add(rel)
 # Flat library modules only; unrelated closure already retained in NNH_seed.
 if not rel.startswith(('LIB_','LIBB_','LIBC_')):continue
 data=p.read_bytes();h=hashlib.sha256(data).hexdigest();assert h==row['sha256'],str(p)
 for src in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not src.is_file():continue
  q=dst/src.name;h=hashlib.sha256(src.read_bytes()).hexdigest()
  if not q.exists():shutil.copy2(src,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h,str(q)
  out.append(dict(source=str(src),destination=str(q),sha256=h,bytes=q.stat().st_size))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='rows='+repr(rows)+'\n'+code,capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'NNH_RESUME_LIBRARY_IMPORTS.json').write_text(r.stdout)
p=E/'NNH_PATHS.json';paths=json.loads(p.read_text());new='/home/dombarker/project-offloads/codex-cx-integrate-20261111/NNH_library_seed'
if new not in paths:paths.append(new)
p.write_text(json.dumps(paths,indent=2)+'\n');print('copied',len(json.loads(r.stdout)))
