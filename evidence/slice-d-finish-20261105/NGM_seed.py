from pathlib import Path
import json,lzma,subprocess,time
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-slice-d-finish-20261105'
C='/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104'
inputs=json.loads(lzma.decompress((E.parent/'ledger8-20261105/NGJ_CLOSURE_PINS.json.xz').read_bytes()))
code="from pathlib import Path\nimport json,subprocess,sys,hashlib,shutil,lzma\nb=Path(B);c=Path(C);b.mkdir(exist_ok=True)\nwith (b/'NGM_SEED-admission.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NGM_SEED-admission.json')],stdout=f,stderr=subprocess.STDOUT)\np=b/'NGM_SEED-admission.json'\nprint(p.read_text() if p.exists() else 'MISSING',flush=True)\nif not p.exists():sys.exit(79)\na=json.loads(p.read_text())\nif r.returncode!=0 or a.get('allowed') is not True:sys.exit(78)\nc.mkdir(exist_ok=True);out=[]\nfor f in inputs['selected_objects']:\n p=Path(f['path']);suffix=str(p).split(f['module'].replace('.','/'))[-1];rel=f['module'].replace('.','/')+suffix\n # NGJ cleanup retained exports in cache rather than rebuildable objects.\n if not p.exists() and '/NGJ_objects/' in str(p):p=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGJ_exports_20261105')/rel\n data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==f['sha256'],str(p)\n q=c/rel;q.parent.mkdir(parents=True,exist_ok=True)\n if not q.exists():q.write_bytes(data)\n assert hashlib.sha256(q.read_bytes()).hexdigest()==f['sha256']\n out.append(dict(f,source=str(p),destination=str(q)))\nw=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')\nfor n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)\nraw=json.dumps(dict(selected=out,paths=len(out),bytes=sum(f['bytes'] for f in out))).encode()\n(b/'NGM_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(b/'NGM_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')\nprint(json.dumps(dict(paths=len(out),bytes=sum(f['bytes'] for f in out))))\n"
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\ninputs='+repr(inputs)+'\n'+code,text=True,capture_output=True)
 (E/f'NGM_SEED-{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout[-1000:],r.stderr[-1500:],flush=True)
 if r.returncode==0:break
 if r.returncode==79 and retry==0:time.sleep(30);continue
 if r.returncode not in [78,255] or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
for n in ['NGM_CACHE_IMPORTS.json.xz','NGM_CACHE_IMPORTS.json.sha256','NGM_SEED-admission.json','NGM_SEED-admission.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
