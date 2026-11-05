"""Private input/receipt orchestrator; unchanged S2W host launcher."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,os
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry-20261105'
B='/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106';H='dombarker@100.108.41.90'
a,kind,target=sys.argv[1:];archive_pattern=('NEP_proof'+str(int(target.split('stage')[1].split('_')[0])-1)+'_*_REACHABLE.txt') if kind=='audit' else ''; assert kind in ['kani','lean','inspect','audit','extract'];assert a.startswith('NHY_'+('K' if kind=='kani' else 'E' if kind=='extract' else 'L'));assert 1<=int(a[-3:])<=(120 if kind=='kani' else 2 if kind=='extract' else 80);assert not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NHY_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted: recover read-only; never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});p=b/{(a+'-reservation.json')!r}
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('Infrastructure STOP: missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('reservation wait',flush=True);time.sleep(180);continue
 raise RuntimeError('Infrastructure STOP: admission')
old=json.loads((P/'NGL_K037.json').read_text());env=dict(old['env']);env['TMPDIR']=B+'/NHY_tmp'
env['LEAN_PATH']=B+'/NHY_objects:/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104/NHY_NHJ_seed:/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104/NHD_exports_20261106:/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104/NHD_NGK_exports_20261106:'+env['LEAN_PATH'].replace('/home/dombarker/project-offloads/codex-cx-slice-d-entry-20261105/NGL_objects','/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104/NGL_exports_20261105')
files={};sources=[]
if kind=='kani' and int(a[-3:])>=43:
 env.update(json.loads((E/'NHY_DEVNET_CONFIG.json').read_text()))
if kind=='kani':
 for n in ['NHY_gate.py','NHY_erasure.py','NHY_SOURCE_PINS.json']:files[n]=(E/n).read_text()
 for n in ['NGL_FROZEN_SOURCE_PINS.json','NGL_ZERO_SOURCE_ERASURE.json','NGL_CONTRACT_ANNOTATIONS.json']:files[n]=(P/n).read_text()
 for n,t in json.loads((E/'NHY_NATIVE_INPUTS.json').read_text()).items():files['NHY_src/'+n]=t
 sources=list(files)+['NHY_src/Cargo.lock']
 command=['python3','NHY_gate.py',a+'.json']
 native=list(old['native_command']);native=[s.replace('/home/dombarker/project-offloads/codex-cx-slice-d-entry-20261105',B).replace('/NGL_src/','/NHY_src/').replace('/NGL_target','/NHY_target') for s in native]
 native[native.index('--harness')+1]=target
 native[native.index('--manifest-path')+1]=B+'/NHY_src/programs/r1-cost-probe/Cargo.toml'
 native[native.index('--features')+1]='pool-adapter,private-leaf-salts'
 cfg=dict(native_command=native,root_package='aspis-r1-cost-probe-program')
elif kind=='extract':
 files['NHY_extract.py']=(E/'NHY_extract.py').read_text();ref='NHY_snapshot_ref.rs' if target=='NHY_SnapshotReference' else 'NHY_ids_ref.rs';files[ref]=(E/(ref+'.txt')).read_text()
 sources=list(files);command=['python3','NHY_extract.py',a+'.json'];cfg={}
elif kind=='inspect':
 name='NHY_host_finalize.py' if target=='NHY_host_finalize' else 'NHY_rodata.py';files[name]=(E/name).read_text();sources=[name];command=['python3',name];cfg={}
elif kind=='audit':
 for name in ['NHY_audit.py','NHY_AUDIT_ROOTS.json','NHY_EXPECTED_IMPORTS.jsonl','NHY_AUDIT_PLAN.json']:files[name]=(E/name).read_text()
 sources=list(files)+['NHY_native/NHY_ProofDriver.c','NHY_native/NHY_ScanDriver.c','NHY_native/NFA_WALKER.c','NHY_native/NFA_MemoryLimit.c'];command=['python3','NHY_audit.py'];cfg={}
else:
 n='NHY_generated/'+target.replace('.','/')+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 T=env['LEAN_SYSROOT'];command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NHY_generated','-o','NHY_objects/'+target.replace('.','/')+'.olean',n];cfg={}
 if target in ['NHY_ProofDriver','NHY_ScanDriver']:command+=['-c','NHY_native/'+target+'.c']
cfg.update(attempt=a,kind=kind,module=target,sources=sources,command=command,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'selected_objects':{}},expected_time='optimized compilation then focused native contract; no field arithmetic' if kind=='kani' else 'raw kernel traversal and NFX source scan; existing optimized binaries reused' if kind=='audit' else 'private retained object export and disk inventory' if kind=='inspect' and target=='NHY_host_finalize' else 'read-only ELF slot inspection' if kind=='inspect' else 'focused Lean elaboration')
files[a+'.json']=json.dumps(cfg)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({json.dumps(files)!r})
(b/'NHY_native').mkdir(exist_ok=True)
if {kind!r}=='lean':(b/'NHY_objects'/{target.replace('.','/')!r}).parent.mkdir(parents=True,exist_ok=True)
if {kind!r}=='audit':
 import shutil
 for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
  q=b/'NHY_native'/name
  if not q.exists():shutil.copy2(Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry2-20261106/NHD_L014/sources/NHD_native')/name,q)
for n,t in files.items():p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
if x['kind'] in ['lean','audit']:
 rels=set()
 for root in roots:
  for stem in ['Aeneas','AeneasMeta']:
   p=Path(root)/stem
   if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
   for suf in ['.olean','.olean.private','.olean.server','.ir']:
    if Path(root,stem+suf).is_file():rels.add(stem+suf)
 if x['kind']=='audit':rels.update(n.replace('.','/')+'.olean' for n in ['NHY_COMBINED_IMPORT','NFA_WALKER','NFA_MemoryLimit','NEP_Planted','NEP_Mutations'])
 for line in ((b/x['sources'][0]).read_text().splitlines() if x['kind']=='lean' else []):
  if line.startswith('import '):rels.update(n.replace('.','/')+'.olean' for n in line[7:].split() if n!='all')
 for rel in sorted(rels):
  p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p is not None,rel
  for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
   if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
 x['deps_fingerprint']['selected_objects']=pins;(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
names += [str(p.relative_to(b)) for pat in ['-graph*','-source*','-lock*','-erasure*'] for p in b.glob(a+pat)]
if {kind!r}=='extract':
 names += [str(p.relative_to(b)) for p in (b/'NHY_extracted'/{target!r}).rglob('*') if p.is_file()]+[a+'-extraction-pins.json']+([a+'.llbc'] if (b/(a+'.llbc')).exists() else [])
if {kind!r}=='inspect':names+=['NHY_HOST_FINAL.json','NHY_CACHE_EXPORT.json'] if {target!r}=='NHY_host_finalize' else ['NHY_RODATA.json']
if {kind!r}=='audit':
 names += [str(p.relative_to(b)) for p in (b/{target!r}).rglob('*') if p.is_file()]
 names += [str(p.relative_to(b)) for p in b.glob({archive_pattern!r})]
 names += ['NHY_LOADED_scan.jsonl']
print(json.dumps({{n:(b/n).read_text() for n in names}}))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,t in out.items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);data=t.encode()
 if n.endswith('.log') or n.endswith('_REACHABLE.txt') or n.endswith('.llbc'):
  (E/(n+'.sha256')).write_text(hashlib.sha256(data).hexdigest()+'\n');(E/(n+'.xz')).write_bytes(lzma.compress(data))
 else:p.write_bytes(data)
assert a+'/receipt.json' in out,'Missing receipt; do not resubmit'
rc=json.loads(out[a+'/receipt.json'])
with (E/'NHY_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(out[a+'/stdout.log'][-2500:]);sys.exit(rc['exit_status'])
