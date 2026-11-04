"""Private serial runner; uses unchanged admitted S2W launcher."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,os
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-d-field2-20261104'
C='/home/dombarker/project-offloads/codex-cx-slice-d-field2-cache-20261104'
W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
H='dombarker@100.108.41.90';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,kind,target=sys.argv[1:];limit=20 if kind=='kani' else 2 if kind=='extract' else 90; assert a.startswith('NGA_') and 1<=int(a[-3:])<=limit
assert not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NGA_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
paths=[B+'/NGA_objects',C+'/NFT_exports_20261104',C+'/NFQ_exports_20261104',C+'/NFN_exports_20261104',C+'/NFM_exports_20261104']+['/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NFQ_exports_20261104', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NFN_exports_20261104', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NFM_exports_20261104', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NFJ_objects', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NCO_objects', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NFG_exports_20261104', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NFG_NFF_objects', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NFB_exports_20261104', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NEW_exports_20261104', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NET_exports_20261104', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NFG_standard_view', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NEB_exports_20261029', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NET_peer_exports', '/home/dombarker/project-offloads/codex-cx-sound-int2-20261025', '/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NEV_exports_20261104', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NEI_exports_20261103', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NEG_results_20261101', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NEG_exports_20261029', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NFB_reconcile_objects', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NER_cohort', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NFE_exports_20261104', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/NFC_audit_support_20261104', '/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean', '/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/fixtures']
env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NGA_tmp',LEAN_PATH=':'.join(paths))
files={};sources=[]
assert target.startswith('NGA_') or kind in ['auditbin','kani','extract','dependency']

if kind=='kani':
 files['NGA_gate.py']=(E/'NGA_gate.py').read_text()
 if (E/'NGA_NATIVE_INPUTS.json').exists():
  for n,t in json.loads(Path(os.environ.get('NGA_INPUT_SET',str(E/'NGA_NATIVE_INPUTS.json'))).read_text()).items():files['NGA_src/'+n]=t
  files['NGA_SOURCE_PINS.json']=Path(os.environ.get('NGA_PIN_SET',str(E/'NGA_SOURCE_PINS.json'))).read_text()
 sources=['NGA_gate.py','NGA_SOURCE_PINS.json','NGA_src/Cargo.lock','NGA_src/Cargo.toml']
 sources += [n for n in files if n.startswith('NGA_src/')]

 command=['python3','NGA_gate.py',a+'.json']
 env.update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 import os
 if os.environ.get('NGA_INVERT'):env['RUSTFLAGS']+=' --cfg NGA_invert'
 if os.environ.get('NGA_BADARG'):env['RUSTFLAGS']+=' --cfg NGA_bad_argument'
elif kind=='extract':
 files['NGA_extract.py']=(E/'NGA_extract.py').read_text();files['NGA_reference.rs.txt']=(E/'NGA_reference.rs.txt').read_text();sources=['NGA_extract.py','NGA_reference.rs.txt'];command=['python3','NGA_extract.py']
 if target=='NGA_ScanReference':
  files={'NGA_scan_extract.py':(E/'NGA_scan_extract.py').read_text(),'NGA_src/programs/r1-cost-probe/src/NGA_scan_reference.rs':(E/'NGA_scan_reference.rs.txt').read_text(),'NGA_SOURCE_PINS.json':(E/'NGA_SOURCE_PINS.json').read_text()};sources=['NGA_scan_extract.py','NGA_src/programs/r1-cost-probe/src/NGA_scan_reference.rs'];command=['python3','NGA_scan_extract.py']
elif kind=='dependency':
 assert target=='JHe_ZeroGate'
 n='NGA_dependencies/'+target+'.lean';files[n]=(E.parent.parent/'lean'/ (target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NGA_dependencies','-o','NGA_objects/'+target+'.olean',n]
elif kind=='lean':
 n='NGA_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NGA_generated','-o','NGA_objects/'+target+'.olean',n]
 if target in ['NGA_Driver','NGA_ProofDriver','NGA_Stage2Driver','NFA_WALKER','NFA_MemoryLimit']:command+=['-c','NGA_native/'+target+'.c']
elif kind=='linkaudit':
 sources=['NGA_native/'+target+'.c','NGA_native/NFA_WALKER.c','NGA_native/NFA_MemoryLimit.c']
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NGA_native/'+target,*sources]
elif kind=='auditbatch' and target=='NGA_Stage2Driver':
 files['NGA_stage2_audit_batch.py']=(E/'NGA_stage2_audit_batch.py').read_text()
 sources=['NGA_generated/NGA_Stage2Driver.lean','NGA_stage2_audit_batch.py','NGA_native/NGA_Stage2Driver.c','NGA_native/NFA_WALKER.c','NGA_native/NFA_MemoryLimit.c']
 command=['python3','NGA_stage2_audit_batch.py']
elif kind=='auditbatch':
 files['NGA_final_audit_batch.py']=(E/'NGA_final_audit_batch.py').read_text()
 sources=['NGA_generated/NGA_ProofDriver.lean','NGA_final_audit_batch.py','NGA_native/NGA_ProofDriver.c','NGA_native/NFA_WALKER.c','NGA_native/NFA_MemoryLimit.c']
 command=['python3','NGA_final_audit_batch.py']
elif kind=='auditbin':
 sources=['NGA_generated/NGA_Driver.lean'];command=['NGA_native/NGA_Driver',target]
else:raise ValueError(kind)
if target in ['scan','queryscan']:
 name='NGA_QUERY_EXPECTED_IMPORTS.jsonl' if target=='queryscan' else 'NGA_EXPECTED_IMPORTS.jsonl'
 files[name]=(E/name).read_text();sources+=[name]
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'selected_objects':{}},expected_time='Focused elaboration' if kind=='lean' else 'Optimized audit linker' if kind=='linkaudit' else 'Raw checked-kernel graph traversal')
if kind=='kani':cfg['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NGA_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NGA_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
if kind=='kani' and os.environ.get('NGA_PROGRAM'):
 cfg['root_package']='aspis-r1-cost-probe-program'
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NGA_src/programs/r1-cost-probe/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]='pool-adapter,private-leaf-salts'
if kind=='kani' and os.environ.get('NGA_CORE'):
 cfg['root_package']='aspis-core'
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NGA_src/crates/aspis-core/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]='r0'
if kind=='kani' and os.environ.get('NGA_STATEMENT'):
 fs=[r['features'] for r in json.loads((E/'NGA_K002-graph-check.json').read_text())['selected_closure'] if r['name']=='aspis-statement'][0]
 fs=[f for f in fs if f!='spend-dynamic-rate512'];cfg['root_package']='aspis-statement';cfg['metadata_features']=','.join('aspis-statement/'+f for f in fs)
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NGA_src/crates/aspis-statement/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]=','.join(fs)
cfg['expected_time']='optimized compilation then scalar contract; no field multiplication' if kind=='kani' else cfg['expected_time']
files[a+'.json']=json.dumps(cfg)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for directory in ['NGA_objects','NGA_tmp','NGA_native']:(b/directory).mkdir(parents=True,exist_ok=True)
(b/'NGA_objects'/{(target+'.olean')!r}).parent.mkdir(parents=True,exist_ok=True)
for support in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=b.parent/'codex-cx-slice-d-define-20261104'/'NFQ_native'/support
 if p.exists():(b/'NGA_native'/support).write_bytes(p.read_bytes())
for support in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=b.parent/'codex-cx-slice-d-define-20261104'/'NFQ_native'/support
 if p.exists():(b/'NGA_native'/support).write_bytes(p.read_bytes())
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
for module in (['NGA_STAGE2_IMPORT' if x['module']=='NGA_Stage2Driver' else 'NGA_COMBINED_IMPORT'] if x['kind']=='auditbatch' else [])+(['NEP_Planted','NEP_Mutations'] if x['module'] in ['NGA_Driver','NGA_ProofDriver','NGA_Stage2Driver','fixtures'] else [])+(['NGA_QueryModel'] if x['kind']=='auditbin' and x['module'].startswith('query') else [])+(['NGA_COMBINED_IMPORT'] if x['kind']=='auditbin' and (x['module'].startswith('proof') or x['module']=='scan') else [])+[n for line in (b/x['sources'][0]).read_text().splitlines() if line.startswith('import ') for n in line[7:].split() if n!='all'] if x['kind'] not in ['linkaudit','kani','extract'] else []:
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
if {kind!r}=='extract':
 if {target!r}=='NGA_ScanReference':names+=['NGA_SCAN_EXTRACTION_PINS.json','NGA_scan_reference.llbc']+[str(p.relative_to(b)) for p in (b/'NGA_scan_extracted').rglob('*') if p.is_file()]
 else:names+=['NGA_EXTRACTION_PINS.json','NGA_reference.llbc']+[str(p.relative_to(b)) for p in (b/'NGA_extracted').rglob('*') if p.is_file()]
names += [str(p.relative_to(b)) for p in b.glob('NEP_*_REACHABLE.txt')] if {kind!r}=='auditbatch' else [str(p.relative_to(b)) for p in b.glob('NEP_'+{target!r}+'_*_REACHABLE.txt')] if {kind!r}=='auditbin' else []
if {kind!r}=='auditbatch':names += [str(p.relative_to(b)) for p in (b/('NGA_stage2_audit' if {target!r}=='NGA_Stage2Driver' else 'NGA_final_audit')).rglob('*') if p.is_file()]
if {target!r} in ['scan','queryscan']:names+=['NGA_QUERY_LOADED_scan.jsonl' if {target!r}=='queryscan' else 'NGA_LOADED_scan.jsonl']
out={{n:(b/n).read_text() for n in names}}
for name in ['NGA_Driver','NGA_ProofDriver','NGA_Stage2Driver']:
 p=b/'NGA_native'/name
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
with (E/'NGA_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(out[a+'/stdout.log'][-4500:]);sys.exit(rc['exit_status'])
