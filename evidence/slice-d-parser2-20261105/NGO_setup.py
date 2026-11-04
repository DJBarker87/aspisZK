from pathlib import Path
import subprocess,json,time,sys
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-d-parser2-20261105'
C='/home/dombarker/project-offloads/codex-cx-slice-d-parser2-cache-20261104'
I='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
H='dombarker@100.108.41.90'
base=json.loads((E.parent/'ledger8-20261105/NGJ_L003.json').read_text())['env']['LEAN_PATH'].split(':')[1:]
old=json.loads((E.parent/'slice-d-parser-20261104/NGD_L067.json').read_text())['env']['LEAN_PATH'].split(':')[1:]
seeds=[('/home/dombarker/project-offloads/codex-cx-slice-d-parser-cache-20261104/NGD_exports_20261104','NGD_exports_20261104'),('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGJ_exports_20261105','NGJ_exports_20261105')]
for cache,export in [('codex-cx-slice-d-define-cache-20261104','NFQ_exports_20261104'),('codex-cx-slice-q-phase-cache-20261104','NFN_exports_20261104'),('codex-cx-slice-q-mul9-cache-20261104','NFM_exports_20261104')]:seeds.append(('/home/dombarker/project-offloads/'+cache+'/'+export,export))
code=f'''from pathlib import Path
import subprocess,json,hashlib,sys,shutil
b=Path({B!r});b.mkdir(exist_ok=True)
with (b/'NGO_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NGO_SETUP-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NGO_SETUP-admission.json';print((b/'NGO_SETUP-barrier.log').read_text())
if not p.exists():sys.exit(79)
a=json.loads(p.read_text());print(json.dumps(dict(admission=a,exit=r.returncode)))
if r.returncode!=0 or a.get('allowed') is not True:sys.exit(78)
c=Path({C!r});c.mkdir(exist_ok=True);imports={{}}
for root,dest in {seeds!r}:
 root=Path(root);assert root.is_dir(),str(root)
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  q=c/dest/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():shutil.copy2(p,q)
  src=hashlib.sha256(p.read_bytes()).hexdigest();dst=hashlib.sha256(q.read_bytes()).hexdigest();assert src==dst
  imports[str(p)]=dict(bytes=p.stat().st_size,sha256=src,selected_path=str(q),selected_sha256=dst)
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:(b/n).write_bytes((Path({I!r})/n).read_bytes())
(b/'NGO_CACHE_IMPORTS.json').write_text(json.dumps(imports,indent=1))
print(json.dumps(dict(seed_files=len(imports),seed_bytes=sum(x['bytes'] for x in imports.values()),launcher_sha256=hashlib.sha256((b/'S2W_run_host.py').read_bytes()).hexdigest())))
'''
for k in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
 (E/f'NGO_SETUP-{k}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:print(r.stdout);break
 if r.returncode==255 and k<10:time.sleep(60);continue
 if r.returncode==78 and k<10:time.sleep(180);continue
 if r.returncode==79 and k==0:time.sleep(30);continue
 sys.exit('STOP shared infrastructure: '+r.stdout+r.stderr)
else:sys.exit('STOP retry exhaustion')
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/NGO_CACHE_IMPORTS.json'],capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'NGO_CACHE_IMPORTS.json').write_text(r.stdout)
paths=[B+'/NGO_objects']+[C+'/'+dest for _,dest in seeds]+base+old
paths=list(dict.fromkeys(paths));(E/'NGO_PATHS.json').write_text(json.dumps(paths,indent=1))
