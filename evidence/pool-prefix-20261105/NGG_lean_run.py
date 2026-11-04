"""Serial lane-owned validation wrapper; host launcher is copied unchanged."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,re
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-pool-prefix-20261104';H='dombarker@100.108.41.90'
a,target=sys.argv[1:3];mode=sys.argv[3] if len(sys.argv)>3 else 'lean';assert mode in ['lean','link','fixtures','final','scan-link','scan','extract'];assert (a.startswith('NGG_B') and 1<=int(a[5:])<=100) or (a.startswith('NGG_E') and 1<=int(a[5:])<=3)
prior=[json.loads(line) for line in (E/'NGG_ATTEMPTS.jsonl').read_text().splitlines()]
assert sum(row['kind'] not in ['kani','extract'] for row in prior)<60 if mode!='extract' else sum(row['kind']=='extract' for row in prior)<2
assert re.fullmatch(r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*',target)
moduleRel=target.replace('.','/')
assert not (E/'NGG_ACTIVE.json').exists();assert not (E/a).exists();active=E/'NGG_B_LEAN_ACTIVE.json';assert not active.exists();active.write_text(json.dumps(dict(attempt=a)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,text=True,capture_output=True)
  with (E/'NGG_B_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<20:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP infrastructure: reservation JSON missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<20:time.sleep(180);continue
 raise SystemExit('STOP infrastructure admission')
local=E/('NGG_reference.rs' if mode=='extract' else moduleRel+'.lean')
imported=E/'NGG_imports'/(moduleRel+'.lean')
source=local.read_text() if local.exists() else imported.read_text() if imported.exists() else json.loads((E/'NFO_UNCHANGED_BUILD_PLAN.json').read_text())['sources'][target]['source']
# Dependency pinning resolves the exact LEAN_PATH order, including the Aeneas library.
code=f'''from pathlib import Path
import re,json,hashlib
b=Path({B!r});coherent=b.parent/'codex-cx-sound-int2-20261025'
cache=b.parent/'codex-cx-pool-prefix-cache-20261104'
roots=[b/'NGG_B_objects',b/'NGG_C_objects',cache/'NGG_headline',cache/'NFV_final_objects_20261104',cache/'NFR_final_objects_20261104',cache/'NFO_final_objects_20261104',cache,*[cache/n for n in ['NEY_final_objects_20261104','NEX_final_objects_20261104','NEQ_final_objects_20261103','NEM_final_objects_20261102']],coherent,coherent/'objects',Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
selected={{}};missing=[];seen=set()
def visit(n):
 if n in seen:return
 seen.add(n);rel=n.replace('.','/')
 p=next((r/(rel+'.olean') for r in roots if (r/(rel+'.olean')).exists()),None)
 if p is None:missing.append(n);return
 selected[str(p)]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 for suffix in ['.private','.server','.ir']:
  companion=Path(str(p)+suffix) if suffix!='.ir' else p.with_suffix('.ir')
  if companion.exists():selected[str(companion)]=dict(path=str(companion),sha256=hashlib.sha256(companion.read_bytes()).hexdigest())
 q=next((r/(rel+'.lean') for r in [b/'NGG_B_generated',b/'NGG_C_generated',*roots] if (r/(rel+'.lean')).exists()),None)
 if q:
  for dep in re.findall(r'^(?:public )?import\\s+(?:all\\s+)?([\\w.]+)',q.read_text(),re.M):visit(dep)
for n in re.findall(r'^(?:public )?import\\s+(?:all\\s+)?([\\w.]+)',{source!r},re.M):visit(n)
for n in ({['NGG_COMBINED_IMPORT'] if mode in ['final','scan'] else ['NEP_Planted','NEP_Mutations'] if mode=='fixtures' else []!r}):visit(n)
for canonical_library_object in [coherent/'objects/Aeneas.olean',*(coherent/'objects/Aeneas').rglob('*.olean')]:
 rel=canonical_library_object.relative_to(coherent/'objects')
 p=next((r/rel for r in roots if (r/rel).exists()),None)
 assert p is not None,('missing resolved Aeneas object',str(rel))
 selected[str(p)]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 for suffix in ['.private','.server','.ir']:
  companion=Path(str(p)+suffix) if suffix!='.ir' else p.with_suffix('.ir')
  if companion.exists():selected[str(companion)]=dict(path=str(companion),sha256=hashlib.sha256(companion.read_bytes()).hexdigest())
if {mode in ['fixtures','final','scan']!r}:
 p=b/({'NFO_native/NGG_Coherence' if mode=='scan' else 'NFO_native/NGG_Driver'!r});selected[str(p)]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
print(json.dumps(dict(selected_objects=selected,missing=missing)))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr;pins=json.loads(r.stdout)
(E/(a+'-pins.json')).write_text(json.dumps(pins,indent=1)+'\n')
if pins['missing']:active.unlink();raise SystemExit('Missing unchanged dependencies: '+str(pins['missing']))
command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NGG_B_generated','-o','NGG_B_objects/'+moduleRel+'.olean','NGG_B_generated/'+moduleRel+'.lean']
if target in ['NFO_WALKER','NFO_MemoryLimit','NFO_Driver','NFO_Coherence','NGG_Driver','NGG_Coherence','NGG_WALKER','NGG_MemoryLimit']:
 command[command.index('-o'):command.index('-o')]=['-c','NFO_native/'+moduleRel+'.c']
if mode=='link':command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NFO_native/NGG_Driver','NFO_native/NGG_Driver.c','/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NFR_audit_native_20261104/NFR_WALKER.c','/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NFR_audit_native_20261104/NFR_MemoryLimit.c']
if mode in ['fixtures','final']:command=['NFO_native/NGG_Driver',mode]
if mode=='final':command=['NFO_native/NGG_Driver','final']
if mode=='scan-link':command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NFO_native/NGG_Coherence','NFO_native/NGG_Coherence.c','/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NFR_audit_native_20261104/NFR_MemoryLimit.c']
if mode=='scan':command=['NFO_native/NGG_Coherence']
if mode=='extract':command=['python3','NGG_extract.py']
cfg=dict(attempt=a,kind='lean' if mode=='lean' else mode,module=target,sources=['NFO_native/NGG_Coherence.c','/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NFR_audit_native_20261104/NFR_MemoryLimit.c'] if mode=='scan-link' else ['NFO_native/NGG_Driver.c','/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NFR_audit_native_20261104/NFR_WALKER.c','/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NFR_audit_native_20261104/NFR_MemoryLimit.c'] if mode=='link' else ['NGG_B_generated/'+moduleRel+'.lean'],command=command,env=dict(LEAN_SYSROOT='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',LEAN_PATH=B+'/NGG_B_objects:'+B+'/NGG_C_objects:/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NGG_headline:/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NFV_final_objects_20261104:/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NFR_final_objects_20261104:/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NFO_final_objects_20261104:/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104:/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NEY_final_objects_20261104:/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NEX_final_objects_20261104:/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NEQ_final_objects_20261103:/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NEM_final_objects_20261102:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=pins)
(E/a).mkdir();(E/a/'NGG_B_SOURCE.lean.txt').write_text(source)
files={'NGG_B_generated/'+moduleRel+'.lean':source,a+'.json':json.dumps(cfg)}
if mode=='extract':
 files.update({'NGG_extract.py':(E/'NGG_extract.py').read_text(),'NGG_ref/Cargo.toml':(E/'NGG_reference_Cargo.toml').read_text(),'NGG_ref/src/lib.rs':(E/'NGG_reference.rs').read_text()})
 cfg['sources']=['NGG_extract.py','NGG_ref/Cargo.toml','NGG_ref/src/lib.rs'];files[a+'.json']=json.dumps(cfg)
code=f'''from pathlib import Path
import json
b=Path({B!r})
(b/{('NGG_B_objects/'+moduleRel+'.olean')!r}).parent.mkdir(parents=True,exist_ok=True)
(b/'NFO_native').mkdir(exist_ok=True)
if {mode=='extract'!r}:
 import shutil
 (b/'NGG_ref').mkdir(exist_ok=True);shutil.copy2(b/'NGG_src/Cargo.lock',b/'NGG_ref/Cargo.lock')
for n,s in json.loads({json.dumps(files)!r}).items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
# Recovery is read-only even after a transport failure; never submit twice.
code=f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in {[a+'/receipt.json',a+'/stdout.log',a+'/time.log']!r} if (b/n).exists()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr;out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'unresolved submitted attempt; never resubmit'
if mode in ['link','scan-link']:
 r=ssh('python3',f"from pathlib import Path;import json;b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in ['NFO_native/NGG_Driver.c','/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NFR_audit_native_20261104/NFR_WALKER.c','/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NFR_audit_native_20261104/NFR_MemoryLimit.c','NFO_native/NGG_Coherence.c'] if (b/n).exists()}}))")
 assert r.returncode==0,r.stderr
 for n,s in json.loads(r.stdout).items():
  if Path(n).is_absolute():continue # Imported C inputs are pinned/reused, never written at a local absolute path.
  p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
rc=json.loads(out[a+'/receipt.json']);
entry={k:v for k,v in rc.items() if k!='deps_fingerprint'}
entry['full_receipt']=dict(path=str(E/a/'receipt.json'),sha256=hashlib.sha256((E/a/'receipt.json').read_bytes()).hexdigest())
with (E/'NGG_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
active.unlink();
from NGG_checkpoint import checkpoint
checkpoint()
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(out[a+'/stdout.log'][-2000:] if rc['exit_status'] else '')

sys.exit(rc["exit_status"])
