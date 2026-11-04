"""Private serial runner; uses unchanged admitted S2W launcher."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-d-checkpoint-20261104'
C='/home/dombarker/project-offloads/codex-cx-slice-d-checkpoint-cache-20261104'
W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
H='dombarker@100.108.41.90';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,kind,target=sys.argv[1:];limit=100 if kind=='kani' else 3 if kind=='extract' else 70; assert a.startswith('NGC_') and 1<=int(a[-3:])<=limit
assert not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NGC_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
paths=[C+'/NFU_exports_20261104',C+'/NFT_exports_20261104',C+'/NFS_exports_20261104',C+'/NFP_exports_20261104',B+'/NGC_objects',C+'/NFQ_exports_20261104',C+'/NFN_exports_20261104',C+'/NFM_exports_20261104',C+'/NFI_exports_20261104',C+'/NFF_exports_20261104',C+'/NFC_exports_20261104',C+'/NFA_exports_20261104',C+'/NFJ_objects',C+'/NCO_objects',C+'/NFG_exports_20261104',C+'/NFG_NFF_objects',C+'/NFB_exports_20261104',C+'/NEW_exports_20261104',C+'/NET_exports_20261104',C+'/NFG_standard_view',C,C+'/NEB_exports_20261029',C+'/NET_peer_exports',C+'/NGC_selected_closure',W,W+'/objects',C+'/NEV_exports_20261104',C+'/NEI_exports_20261103',C+'/NEG_results_20261101',C+'/NEG_exports_20261029',C+'/NFB_reconcile_objects',C+'/NER_cohort',C+'/NFE_exports_20261104',C+'/NFC_audit_support_20261104',C+'/fixtures',T+'/lib/lean']
# Explicit fixture and unchanged support objects, selected only if not in private cache.
paths+=json.loads((E/'NGC_FIXTURE_PATHS.json').read_text()) if (E/'NGC_FIXTURE_PATHS.json').exists() else []
env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NGC_tmp',LEAN_PATH=':'.join(paths))
files={};sources=[]
assert target.startswith('NGC_') or kind in ['auditbin','kani','extract','dependency']

if kind=='kani':
 files['NGC_gate.py']=(E/'NGC_gate.py').read_text()
 if (E/'NGC_NATIVE_INPUTS.json').exists():
  for n,t in json.loads((E/'NGC_NATIVE_INPUTS.json').read_text()).items():files['NGC_src/'+n]=t
  files['NGC_SOURCE_PINS.json']=(E/'NGC_SOURCE_PINS.json').read_text()
 sources=['NGC_gate.py','NGC_SOURCE_PINS.json','NGC_src/Cargo.lock','NGC_src/Cargo.toml','NGC_src/crates/aspis-r1-cost-probe/src/compact.rs','NGC_src/crates/aspis-r1-cost-probe/src/r1_wire.rs','NGC_src/crates/aspis-r1-cost-probe/src/transport.rs','NGC_src/crates/aspis-r1-cost-probe/src/verifier.rs']
 sources += [n for n in files if n.startswith('NGC_src/')]

 command=['python3','NGC_gate.py',a+'.json']
 env.update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 import os
 if os.environ.get('NGC_INVERT'):env['RUSTFLAGS']+=' --cfg NGC_invert'
elif kind=='extract':
 files['NGC_extract.py']=(E/'NGC_extract.py').read_text()
 files['NGC_references.rs']=(E/'NGC_references.rs.txt').read_text()
 sources=['NGC_extract.py','NGC_references.rs'];command=['python3','NGC_extract.py',a+'.json']
elif kind=='dependency':
 assert target=='JHe_ZeroGate'
 n='NGC_dependencies/'+target+'.lean';files[n]=(E.parent.parent/'lean'/ (target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NGC_dependencies','-o','NGC_objects/'+target+'.olean',n]
elif kind=='lean':
 n='NGC_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NGC_generated','-o','NGC_objects/'+target+'.olean',n]
 if target in ['NGC_WALKER','NGC_MemoryLimit','NGC_Driver','NGC_ProofDriver','NGC_Stage2Driver','NFA_WALKER','NFA_MemoryLimit']:command+=['-c','NGC_native/'+target+'.c']
elif kind=='linkaudit':
 sources=['NGC_native/'+target+'.c','NGC_native/NGC_WALKER.c','NGC_native/NGC_MemoryLimit.c']
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NGC_native/'+target,*sources]
elif kind=='auditbatch' and target=='NGC_Stage2Driver':
 files['NGC_stage2_audit_batch.py']=(E/'NGC_stage2_audit_batch.py').read_text()
 sources=['NGC_generated/NGC_Stage2Driver.lean','NGC_stage2_audit_batch.py','NGC_native/NGC_Stage2Driver.c','NGC_native/NGC_WALKER.c','NGC_native/NGC_MemoryLimit.c']
 command=['python3','NGC_stage2_audit_batch.py']
elif kind=='auditbatch':
 files['NGC_final_audit_batch.py']=(E/'NGC_final_audit_batch.py').read_text()
 sources=['NGC_generated/NGC_ProofDriver.lean','NGC_final_audit_batch.py','NGC_native/NGC_ProofDriver.c','NGC_native/NGC_WALKER.c','NGC_native/NGC_MemoryLimit.c']
 command=['python3','NGC_final_audit_batch.py']
elif kind=='auditbin':
 sources=['NGC_generated/NGC_Driver.lean'];command=['NGC_native/NGC_Driver',target]
else:raise ValueError(kind)
if target in ['scan','queryscan']:
 name='NGC_QUERY_EXPECTED_IMPORTS.jsonl' if target=='queryscan' else 'NGC_EXPECTED_IMPORTS.jsonl'
 files[name]=(E/name).read_text();sources+=[name]
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'selected_objects':{}},expected_time='Focused elaboration' if kind=='lean' else 'Optimized audit linker' if kind=='linkaudit' else 'Raw checked-kernel graph traversal')
if kind=='kani':cfg['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NGC_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NGC_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
if kind=='kani' and os.environ.get('NGC_PROGRAM'):
 cfg['root_package']='aspis-r1-cost-probe-program'
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NGC_src/programs/r1-cost-probe/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]='pool-adapter,private-leaf-salts'
if kind=='kani' and os.environ.get('NGC_CORE'):
 cfg['root_package']='aspis-core'
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NGC_src/crates/aspis-core/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]='r0'
if kind=='kani' and os.environ.get('NGC_STATEMENT'):
 fs=[r['features'] for r in json.loads((E/'NGC_K002-graph-check.json').read_text())['selected_closure'] if r['name']=='aspis-statement'][0]
 fs=[f for f in fs if f!='spend-dynamic-rate512'];cfg['root_package']='aspis-statement';cfg['metadata_features']=','.join('aspis-statement/'+f for f in fs)
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NGC_src/crates/aspis-statement/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]=','.join(fs)
cfg['expected_time']='optimized compilation then scalar contract; no field multiplication' if kind=='kani' else 'optimized Charon frontend, then Aeneas emission; no arithmetic gate' if kind=='extract' else cfg['expected_time']
files[a+'.json']=json.dumps(cfg)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for directory in ['NGC_objects','NGC_tmp','NGC_native']:(b/directory).mkdir(parents=True,exist_ok=True)
(b/'NGC_objects'/{(target+'.olean')!r}).parent.mkdir(parents=True,exist_ok=True)
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
for module in (['NGC_STAGE2_IMPORT' if x['module']=='NGC_Stage2Driver' else 'NGC_COMBINED_IMPORT'] if x['kind']=='auditbatch' else [])+(['NEP_Planted','NEP_Mutations'] if x['module'] in ['NGC_Driver','NGC_ProofDriver','NGC_Stage2Driver','fixtures'] else [])+(['NGC_QueryModel'] if x['kind']=='auditbin' and x['module'].startswith('query') else [])+(['NGC_COMBINED_IMPORT'] if x['kind']=='auditbin' and (x['module'].startswith('proof') or x['module']=='scan') else [])+[n for line in (b/x['sources'][0]).read_text().splitlines() if line.startswith('import ') for n in line[7:].split() if n!='all'] if x['kind'] not in ['linkaudit','kani','extract'] else []:
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
if {kind!r}=='extract':names += [a+'-extraction-pins.json',a+'.llbc']+[str(p.relative_to(b)) for p in (b/'NGC_extracted'/{target!r}).rglob('*') if p.is_file()]
names += [str(p.relative_to(b)) for p in b.glob('NEP_*_REACHABLE.txt')] if {kind!r}=='auditbatch' else [str(p.relative_to(b)) for p in b.glob('NEP_'+{target!r}+'_*_REACHABLE.txt')] if {kind!r}=='auditbin' else []
if {kind!r}=='auditbatch':names += [str(p.relative_to(b)) for p in (b/('NGC_stage2_audit' if {target!r}=='NGC_Stage2Driver' else 'NGC_final_audit')).rglob('*') if p.is_file()]
if {target!r} in ['scan','queryscan']:names+=['NGC_QUERY_LOADED_scan.jsonl' if {target!r}=='queryscan' else 'NGC_LOADED_scan.jsonl']
out={{n:(b/n).read_text() for n in names}}
for name in ['NGC_Driver','NGC_ProofDriver','NGC_Stage2Driver']:
 p=b/'NGC_native'/name
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
with (E/'NGC_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(out[a+'/stdout.log'][-4500:]);sys.exit(rc['exit_status'])
