from pathlib import Path
import subprocess,json,hashlib,lzma,time
E=Path(__file__).resolve().parent
P=E.parent/'owner-dedupe-20261107'
B='/home/dombarker/project-offloads/codex-cx-ledger12-20261107'
C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIR_20261107'
paths=json.loads((E.parent/'l159-physical-20261107/NIN_RESTORE_PATHS.json').read_text())
paths=[p for p in paths if '/codex-cx-l159-physical-20261107/NIN_objects' not in p]
paths=[C,C+'/NIM_seed',C+'/NIN_seed',C+'/NIG_seed','/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIM_flat']+paths
nig=json.loads((E.parent/'slice-d-pair4-20261107/NIG_L080.json').read_text())['env']['LEAN_PATH'].split(':')
paths+= [p for p in nig if not p.endswith('/NIG_objects')]
paths=list(dict.fromkeys(paths));(E/'NIR_PATHS.json').write_text(json.dumps(paths,indent=1)+'\n')
imports=[json.loads((P/'NIM_EXPORT.json').read_text()),json.loads((E.parent/'l159-physical-20261107/NIN_EXPORT.json').read_text()),json.loads((E.parent/'slice-d-pair4-20261107/NIG_EXPORT.json').read_text())]
seeds=[]
for tag,d in zip(['NIM','NIN','NIG'],imports):
 for row in d.get('files',d.get('exports',[])):
  seeds.append(dict(tag=tag,path=row['path'],sha256=row['sha256'],bytes=row['bytes']))
code='''from pathlib import Path
import subprocess,json,sys,hashlib,shutil,lzma
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NIR_seed-admission.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NIR_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NIR_seed-admission.json').read_text());print(json.dumps(dict(exit=r.returncode,reservation=a)),flush=True)
if r.returncode or a.get('allowed') is not True:sys.exit(78)
c=Path(C);c.mkdir(exist_ok=True);rows=[]
for row in seeds:
 p=Path(row['path']);raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==row['sha256'],str(p)
 # Exports contain module subdirectories only for dotted map modules.
 rel=p.relative_to(p.parents[0])
 if p.parent.name=='NIM_MapReference':rel=Path('NIM_MapReference')/p.name
 q=c/(row['tag']+'_seed')/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==row['sha256']
 rows.append(dict(row,destination=str(q)))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
x=dict(files=rows,bytes=sum(r['bytes']for r in rows),admission=a,exit=r.returncode)
(b/'NIR_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x).encode()));print(json.dumps(dict(bytes=x['bytes'],files=len(rows),disk=shutil.disk_usage(b)._asdict())))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nseeds='+repr(seeds)+'\n'+code,text=True,capture_output=True)
 (E/f'NIR_seed-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode in [78,255] and retry<10:time.sleep(180 if r.returncode==78 else 60);continue
 raise RuntimeError(r.stderr+r.stdout[-1000:])
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat '+B+'/NIR_CACHE_IMPORTS.json.xz'],capture_output=True);assert r.returncode==0;(E/'NIR_CACHE_IMPORTS.json.xz').write_bytes(r.stdout)
s=(P/'NIM_run.py').read_text().replace('NIM_','NIR_').replace('codex-cx-owner-dedupe-20261107','codex-cx-ledger12-20261107').replace("C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIR_flat'",'C='+repr(C))
a="[B+'/NIR_objects',C,'/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NII_flat',W,W+'/objects',T+'/lib/lean']"
s=s.replace(a,"[B+'/NIR_objects']+json.loads((E/'NIR_PATHS.json').read_text())")
s=s.replace("print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print((E/a/'stdout.log').read_text()[-3500:])","print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}))")
(E/'NIR_run.py').write_text(s)
print('NIR setup complete',json.loads(lzma.decompress(r.stdout))['bytes'])
