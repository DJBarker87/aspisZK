from pathlib import Path
import json,subprocess,hashlib,lzma,re,time
E=Path(__file__).resolve().parent;P=E.parent/'ledger12-20261107'
B='/home/dombarker/project-offloads/codex-cx-ledger13-20261107';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIU_20261107'
specs=[('ledger12-20261107','NIR'),('slice-d-entry6-20261107','NIS'),('verify-observed4-20261107','NIH'),('slice-d-pair6-20261107','NIT'),('tx2-native3-20261107','NIL'),('pool-borrow2-20261107','NIO')]
seeds=[];extra=[]
for folder,pre in specs:
 p=E.parent/folder;x=json.loads((p/f'{pre}_EXPORT.json').read_text())
 for row in x.get('files',x.get('exports',x.get('own_exports',[]))):
  src=row.get('destination',row.get('path',x.get('path','')+'/'+row.get('name','')))
  seeds.append(dict(tag=pre,path=src,sha256=row['sha256'],bytes=row['bytes']))
 if pre=='NIR':continue
 path=p/f'{pre}_CONSUMER_PATHS.json'
 if path.exists():paths=json.loads(path.read_text())
 else:
  cfgs=[]
  for f in p.glob(f'{pre}_L[0-9][0-9][0-9].json'):
   q=json.loads(f.read_text())
   if 'LEAN_PATH'in q.get('env',{}):cfgs.append((f.name,q['env']['LEAN_PATH'].split(':')))
  paths=sorted(cfgs)[-1][1]
 extra+=paths
paths=[C+'/'+pre+'_seed' for _,pre in specs]+json.loads((P/'NIR_PATHS.json').read_text())+extra
paths=list(dict.fromkeys(paths));(E/'NIU_PATHS.json').write_text(json.dumps(paths,indent=1)+'\n')
code='''from pathlib import Path
import json,subprocess,sys,hashlib,shutil,lzma
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NIU_seed-admission.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NIU_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NIU_seed-admission.json'
if not p.exists():print('MISSING');sys.exit(79)
a=json.loads(p.read_text());print(json.dumps(dict(exit=r.returncode,reservation=a)),flush=True)
if r.returncode or a.get('allowed') is not True:sys.exit(78)
c=Path(C);c.mkdir(exist_ok=True);rows=[]
for row in seeds:
 p=Path(row['path']);assert p.is_file(),str(p)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
 q=c/(row['tag']+'_seed')/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==row['sha256']
 rows.append(dict(row,destination=str(q)))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
x=dict(files=rows,bytes=sum(r['bytes']for r in rows),admission=a,exit=r.returncode,disk=shutil.disk_usage(b)._asdict())
(b/'NIU_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x).encode()));print(json.dumps(dict(bytes=x['bytes'],files=len(rows),disk=x['disk'])))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nseeds='+repr(seeds)+'\n'+code,text=True,capture_output=True)
 (E/f'NIU_seed-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode in [78,255,79] and retry<10:time.sleep(180 if r.returncode==78 else 60 if r.returncode==255 else 30);continue
 raise RuntimeError(r.stdout[-1000:]+r.stderr)
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat '+B+'/NIU_CACHE_IMPORTS.json.xz'],capture_output=True);assert r.returncode==0;(E/'NIU_CACHE_IMPORTS.json.xz').write_bytes(r.stdout)
s=(P/'NIR_run.py').read_text().replace('NIR_','NIU_').replace('codex-cx-ledger12-20261107','codex-cx-ledger13-20261107')
s=s.replace("C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIU_20261107'",'C='+repr(C))
s=s.replace("TMPDIR=B+'/NIU_tmp',LEAN_PATH=", "TMPDIR=B+'/NIU_tmp',CARGO_TARGET_DIR=B+'/NIU_target',LEAN_PATH=")
s=s.replace("if target in ['NIU_Driver','NIU_ProofDriver','NIU_PoolProofDriver','NIU_PoolDriver']", "if target in ['NIU_Driver','NIU_ProofDriver','NIU_PoolProofDriver','NIU_PoolDriver']")
(E/'NIU_run.py').write_text(s)
print(json.dumps(dict(stage='seed',files=len(seeds),bytes=json.loads(lzma.decompress(r.stdout))['bytes'])))
