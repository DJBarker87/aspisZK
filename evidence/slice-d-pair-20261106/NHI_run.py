"""Private serial runner; uses unchanged admitted S2W launcher."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-d-pair-20261106'
C='/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104'
W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
H='dombarker@100.108.41.90';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,kind,target=sys.argv[1:];limit=120 if kind=='kani' else 3 if kind=='extract' else 90; assert a.startswith('NHI_') and 1<=int(a[-3:])<=limit
assert not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NHI_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r})
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r}; print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('STOP missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  print('reservation wait',flush=True);time.sleep(180);continue
 raise RuntimeError('STOP admission')
paths=[B+'/NHI_objects',C+'/NHE_exports_20261106/objects',C+'/NGW_exports_20261105/objects',C+'/NGW_NGK_seed',C+'/NGM_exports_20261105',C,W,W+'/objects',T+'/lib/lean']
env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NHI_tmp',LEAN_PATH=':'.join(paths))
files={};sources=[]
assert target.startswith('NHI_') or kind in ['auditbin','kani','extract','dependency']

if kind=='kani':
 files['NHI_gate.py']=(E/'NHI_gate.py').read_text()
 import runpy
 prepared=runpy.run_path(str(E/'NHI_native_prepare.py'))
 for n,t in prepared['inputs'].items():files['NHI_src/'+n]=t
 files['NHI_SOURCE_PINS.json']=json.dumps(prepared['pins'])
 sources=['NHI_gate.py','NHI_SOURCE_PINS.json','NHI_src/Cargo.lock','NHI_src/Cargo.toml']+[n for n in files if n.startswith('NHI_src/')]
 command=['python3','NHI_gate.py',a+'.json']
 env.update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 import os
 if os.environ.get('NHI_INVERT'):
  flag=os.environ.get('NHI_NATIVE_CFG','NHI_invert');assert flag in ['NHI_invert','NGM_invert'];env['RUSTFLAGS']+=' --cfg '+flag
elif kind=='extract':
 files['NHI_extract.py']=(E/'NHI_extract.py').read_text()
 name={'NHI_TensorRef':'NHI_tensor_reference.rs.patch','NHI_GroupRef':'NHI_group_reference.rs.patch'}[target]
 patch=(E/name).read_text()
 files['NHI_references.rs']=''.join(l[1:]for l in patch.splitlines(True)if l.startswith('+')and not l.startswith('+++'))
 sources=['NHI_extract.py','NHI_references.rs'];command=['python3','NHI_extract.py',a+'.json']
elif kind=='dependency':
 assert target=='JHe_ZeroGate'
 n='NHI_dependencies/'+target+'.lean';files[n]=(E.parent.parent/'lean'/ (target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NHI_dependencies','-o','NHI_objects/'+target+'.olean',n]
elif kind=='lean':
 n='NHI_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NHI_generated','-o','NHI_objects/'+target+'.olean',n]
 if target in ['NHI_Driver','NHI_ProofDriver','NHI_Stage2Driver','NFA_WALKER','NFA_MemoryLimit']:command+=['-c','NHI_native/'+target+'.c']
elif kind=='linkaudit':
 for n in ['NFA_WALKER','NFA_MemoryLimit']:files['NHI_native/'+n+'.c']=(E/('NHI_'+n+'.c.txt')).read_text()
 sources=['NHI_native/'+target+'.c','NHI_native/NFA_WALKER.c','NHI_native/NFA_MemoryLimit.c']
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NHI_native/'+target,*sources]
elif kind=='auditbatch':
 for n in ['NHI_audit_batch.py','NHI_AUDIT_ROOTS.json','NHI_EXPECTED_IMPORTS.jsonl']:
  files[n]=(E/n).read_text()
 sources=['NHI_generated/NHI_ProofDriver.lean','NHI_generated/NHI_Driver.lean','NHI_audit_batch.py','NHI_AUDIT_ROOTS.json','NHI_EXPECTED_IMPORTS.jsonl','NHI_native/NHI_ProofDriver.c','NHI_native/NHI_Driver.c','NHI_native/NFA_WALKER.c','NHI_native/NFA_MemoryLimit.c']
 command=['python3','NHI_audit_batch.py']
elif kind=='auditbin':
 import os
 own=os.environ.get('NHI_AUDIT')=='1'
 driver='NGW_ProofDriver' if target.startswith('proof') or target=='fixtures' else 'NGW_Driver'
 if own:driver=driver.replace('NGW_','NHI_')
 sources=['NHI_inputs/'+driver+'.lean'];files[sources[0]]=((E if own else E.parent/'slice-d-finish2-20261105')/(driver+'.lean')).read_text();command=['NHI_native/'+driver,target]
 if target.startswith('proof'):
  files['NHI_AUDIT_ROOTS.json']=(E/'NHI_AUDIT_ROOTS.json').read_text();sources+=['NHI_AUDIT_ROOTS.json']
else:raise ValueError(kind)
if target in ['scan','queryscan']:
 name='NHI_EXPECTED_IMPORTS.jsonl' if own else 'NGW_EXPECTED_IMPORTS.jsonl'
 files[name]=((E if own else E.parent/'slice-d-finish2-20261105')/name).read_text();sources+=[name]
cfg=dict(attempt=a,own_audit=(kind=='auditbin' and own),kind=kind,module=target,sources=sources,command=command,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'selected_objects':{}},expected_time='Focused elaboration' if kind=='lean' else 'Optimized audit linker' if kind=='linkaudit' else 'Raw checked-kernel graph traversal')
if kind=='kani':cfg['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NHI_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NHI_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
if kind=='kani' and os.environ.get('NHI_PROGRAM'):
 cfg['root_package']='aspis-r1-cost-probe-program'
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NHI_src/programs/r1-cost-probe/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]='pool-adapter,private-leaf-salts'
if kind=='kani' and os.environ.get('NHI_CORE'):
 cfg['root_package']='aspis-core'
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NHI_src/crates/aspis-core/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]='r0'
if kind=='kani' and os.environ.get('NHI_STATEMENT'):
 fs=[r['features'] for r in json.loads((E/'NHI_K002-graph-check.json').read_text())['selected_closure'] if r['name']=='aspis-statement'][0]
 fs=[f for f in fs if f!='spend-dynamic-rate512'];cfg['root_package']='aspis-statement';cfg['metadata_features']=','.join('aspis-statement/'+f for f in fs)
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NHI_src/crates/aspis-statement/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]=','.join(fs)
cfg['expected_time']='optimized compilation then scalar contract; no field multiplication' if kind=='kani' else 'optimized Charon frontend, then Aeneas emission; no arithmetic gate' if kind=='extract' else cfg['expected_time']
files[a+'.json']=json.dumps(cfg)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for directory in ['NHI_objects','NHI_tmp','NHI_native']:(b/directory).mkdir(parents=True,exist_ok=True)
(b/'NHI_objects'/{(target+'.olean')!r}).parent.mkdir(parents=True,exist_ok=True)
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
# Pin all actual selected Aeneas library objects plus direct imports and support.
rels=set()
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
  for suf in ['.olean','.olean.private','.olean.server','.ir']:
   if Path(root,stem+suf).is_file():rels.add(stem+suf)
for rel in sorted(rels):
 p=next(Path(root)/rel for root in roots if (Path(root)/rel).is_file());pins[str(p)]={{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}}
for module in (['NHI_COMBINED_IMPORT'] if x['kind']=='auditbatch' else [])+(['NEP_Planted','NEP_Mutations'] if x['module'] in ['NHI_Driver','NHI_ProofDriver','NHI_Stage2Driver','fixtures'] else [])+(['NHI_QueryModel'] if x['kind']=='auditbin' and x['module'].startswith('query') else [])+([('NHI_COMBINED_IMPORT' if x.get('own_audit') else 'NGW_COMBINED_IMPORT')] if x['kind']=='auditbin' and (x['module'].startswith('proof') or x['module']=='scan') else [])+[n for line in (b/x['sources'][0]).read_text().splitlines() if line.startswith('import ') for n in line[7:].split() if n!='all'] if x['kind'] not in ['linkaudit','kani','extract'] else []:
 rel=module.replace('.','/')+'.olean';p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
 assert p is not None,module
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
x['deps_fingerprint']['selected_objects']=pins;(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
names += [str(p.relative_to(b)) for p in b.glob(a+'-graph*')]+[str(p.relative_to(b)) for p in b.glob(a+'-source*')]+[str(p.relative_to(b)) for p in b.glob(a+'-lock*')] if {kind!r}=='kani' else []
if {kind!r}=='extract':names += [a+'-extraction-pins.json',a+'.llbc']+[str(p.relative_to(b)) for p in (b/'NHI_extracted'/{target!r}).rglob('*') if p.is_file()]
names += [str(p.relative_to(b)) for p in b.glob('NEP_*_REACHABLE.txt')] if {kind!r}=='auditbatch' else [str(p.relative_to(b)) for p in b.glob('NEP_'+{target!r}+'_*_REACHABLE.txt')] if {kind!r}=='auditbin' else []
if {kind!r}=='auditbatch':names += [str(p.relative_to(b)) for p in (b/'NHI_final_audit').rglob('*') if p.is_file()]
if {target!r} in ['scan','queryscan']:names+=['NHI_LOADED_scan.jsonl' if {kind!r}=='auditbin' and {cfg.get('own_audit')!r} else 'NGW_LOADED_scan.jsonl']
out={{n:(b/n).read_text() for n in names}}
for name in ['NGW_Driver','NGW_ProofDriver','NHI_Driver','NHI_ProofDriver']:
 p=b/'NHI_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,t in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
# Archive raw graphs immediately; keep their uncompressed hashes for replay.
if kind in ['auditbin','auditbatch']:
 import lzma
 for name in out:
  if name.startswith('NEP_') and name.endswith('_REACHABLE.txt'):
   p=E/name;data=p.read_bytes();(E/(name+'.sha256')).write_text(hashlib.sha256(data).hexdigest()+'  '+name+'\n')
   (E/(name+'.xz')).write_bytes(lzma.compress(data,preset=6));p.unlink()
assert a+'/receipt.json' in out,'Missing receipt; no resubmit'
rc=json.loads(out[a+'/receipt.json'])
with (E/'NHI_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print('\n'.join(line for line in out[a+'/stdout.log'].splitlines() if 'error:' in line or 'depends on axioms:' in line or 'VERIFICATION:' in line or 'Verification Time:' in line));sys.exit(rc['exit_status'])
