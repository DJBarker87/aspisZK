"""Private serial runner; uses unchanged admitted S2W launcher."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-d-entry-20261105'
C='/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104'
W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
H='dombarker@100.108.41.90';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,kind,target=sys.argv[1:];limit=120 if kind=='kani' else 3 if kind=='extract' else 70; assert a.startswith('NGL_') and 1<=int(a[-3:])<=limit
assert not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NGL_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
paths=[B+'/NGL_objects',C+'/NGJ_exports_20261105',C+'/NGI_exports_20261105',C+'/NFT_exports_20261104',C+'/NFU_exports_20261104',C+'/NFV_final_objects_20261104',C+'/NGE_exports_20261104',C+'/NGF_exports_20261104',C+'/NFY_exports_20261104',C+'/NFY_priority',W,W+'/objects',C+'/NGJ_d_fallback/NFQ_exports_20261104',C+'/NGJ_d_fallback',C+'/NGJ_pool_fallback/NFR_final_objects_20261104',C+'/NGJ_pool_fallback/NFO_final_objects_20261104',C+'/NGJ_pool_fallback',C+'/NGJ_pool_fallback/NEY_final_objects_20261104',C+'/NGJ_pool_fallback/NEX_final_objects_20261104',C+'/NGJ_pool_fallback/NEQ_final_objects_20261103',C+'/NGJ_pool_fallback/NEM_final_objects_20261102',C+'/NGJ_pool_fallback/NEU_final_objects_20261104',C,T+'/lib/lean']
# Explicit fixture and unchanged support objects, selected only if not in private cache.
paths+=json.loads((E/'NGL_FIXTURE_PATHS.json').read_text()) if (E/'NGL_FIXTURE_PATHS.json').exists() else []
env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NGL_tmp',LEAN_PATH=':'.join(paths))
files={};sources=[]
assert target.startswith('NGL_') or kind in ['auditbin','kani','extract','dependency']

if kind=='kani':
 files['NGL_gate.py']=(E/'NGL_gate.py').read_text()
 for n in ['NGL_erasure.py','NGL_FROZEN_SOURCE_PINS.json','NGL_ZERO_SOURCE_ERASURE.json','NGL_CONTRACT_ANNOTATIONS.json']:files[n]=(E/n).read_text()
 if (E/'NGL_NATIVE_INPUTS.json').exists():
  for n,t in json.loads((E/'NGL_NATIVE_INPUTS.json').read_text()).items():files['NGL_src/'+n]=t
  files['NGL_SOURCE_PINS.json']=(E/'NGL_SOURCE_PINS.json').read_text()
 sources=['NGL_CONTRACT_ANNOTATIONS.json','NGL_erasure.py','NGL_FROZEN_SOURCE_PINS.json','NGL_ZERO_SOURCE_ERASURE.json','NGL_gate.py','NGL_SOURCE_PINS.json','NGL_src/Cargo.lock','NGL_src/Cargo.toml','NGL_src/crates/aspis-r1-cost-probe/src/compact.rs','NGL_src/crates/aspis-r1-cost-probe/src/r1_wire.rs','NGL_src/crates/aspis-r1-cost-probe/src/transport.rs','NGL_src/crates/aspis-r1-cost-probe/src/verifier.rs']
 sources += [n for n in files if n.startswith('NGL_src/')]
 sources += ['NGL_src/crates/aspis-r1-cost-probe/src/'+n+'.rs' for n in ['NGL_reference','NGL_compact','NGL_wire','NGL_transport','NGL_verifier']]
 command=['python3','NGL_gate.py',a+'.json']
 env.update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 import os
 if os.environ.get('NGL_INVERT'):env['RUSTFLAGS']+=' --cfg NGL_invert'
 if os.environ.get('NGL_RECORD_CASE') in ['borrow','rejected']:env['RUSTFLAGS']+=' --cfg NGL_record_'+os.environ['NGL_RECORD_CASE']
 if os.environ.get('NGL_FALSE_TARGET') in ['length','data','checkpoint']:env['RUSTFLAGS']+=' --cfg NGL_false_'+os.environ['NGL_FALSE_TARGET']
 if os.environ.get('NGL_CAP') in ['1768','1880','384','192','768','128','256','320']:env['RUSTFLAGS']+=' --cfg NGL_cap_'+os.environ['NGL_CAP']
 if os.environ.get('NGL_DISTINCT_EXIT'):env['RUSTFLAGS']+=' --cfg NGL_distinct_exit'
 if os.environ.get('NGL_GUARD_FALSE'):env['RUSTFLAGS']+=' --cfg NGL_guard_false'
elif kind=='deltaaudit':
 files['NGL_delta_audit.py']=(E/'NGL_delta_audit.py').read_text();files['NGL_AUDIT_ROOTS.json']=(E/'NGL_AUDIT_ROOTS.json').read_text();sources=['NGL_delta_audit.py','NGL_AUDIT_ROOTS.json'];command=['python3','NGL_delta_audit.py']
elif kind=='review':
 files['NGL_review_gate.py']=(E/'NGL_review_gate.py').read_text();files['NGL_review_bundle.sha256']=(E/'NGL_review_bundle.sha256').read_text();sources=['NGL_review_gate.py','NGL_review_bundle.sha256'];command=['python3','NGL_review_gate.py',target.removeprefix('NGL_')]
elif kind=='pins':
 files['NGL_toolpins.py']=(E/'NGL_toolpins.py').read_text();sources=['NGL_toolpins.py'];command=['python3','NGL_toolpins.py']
elif kind=='extract':
 files['NGL_extract.py']=(E/'NGL_extract.py').read_text()
 files['NGL_references.rs']=(E/'NGL_references.rs.txt').read_text()
 sources=['NGL_extract.py','NGL_references.rs'];command=['python3','NGL_extract.py',a+'.json']
elif kind=='dependency':
 assert target=='JHe_ZeroGate'
 n='NGL_dependencies/'+target+'.lean';files[n]=(E.parent.parent/'lean'/ (target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NGL_dependencies','-o','NGL_objects/'+target.replace('.','/')+'.olean',n]
elif kind=='lean':
 n='NGL_generated/'+target.replace('.','/')+'.lean'
 source=E/json.loads((E/'NGL_GENERATED_INPUTS.json').read_text())[target] if target in json.loads((E/'NGL_GENERATED_INPUTS.json').read_text()) else E/(target+'.lean')
 files[n]=source.read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NGL_generated','-o','NGL_objects/'+target.replace('.','/')+'.olean',n]
 if target in ['NGL_Driver','NGL_ProofDriver','NGL_Stage2Driver','NFA_WALKER','NFA_MemoryLimit']:command+=['-c','NGL_native/'+target+'.c']
elif kind=='linkaudit':
 sources=['NGL_native/'+target+'.c','NGL_native/NFA_WALKER.c','NGL_native/NFA_MemoryLimit.c']
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NGL_native/'+target,*sources]
elif kind=='auditbatch' and target=='NGL_Stage2Driver':
 files['NGL_stage2_audit_batch.py']=(E/'NGL_stage2_audit_batch.py').read_text()
 sources=['NGL_generated/NGL_Stage2Driver.lean','NGL_stage2_audit_batch.py','NGL_native/NGL_Stage2Driver.c','NGL_native/NFA_WALKER.c','NGL_native/NFA_MemoryLimit.c']
 command=['python3','NGL_stage2_audit_batch.py']
elif kind=='auditbatch':
 files['NGL_final_audit_batch.py']=(E/'NGL_final_audit_batch.py').read_text()
 sources=['NGL_generated/NGL_ProofDriver.lean','NGL_final_audit_batch.py','NGL_native/NGL_ProofDriver.c','NGL_native/NFA_WALKER.c','NGL_native/NFA_MemoryLimit.c']
 command=['python3','NGL_final_audit_batch.py']
elif kind=='auditbin':
 sources=['NGL_generated/NGL_Driver.lean'];command=['NGL_native/NGL_Driver',target]
else:raise ValueError(kind)
if kind=='auditbatch':
 files['NGL_AUDIT_ROOTS.json']=(E/'NGL_AUDIT_ROOTS.json').read_text();sources+=['NGL_AUDIT_ROOTS.json']
if target in ['scan','queryscan']:
 name='NGL_QUERY_EXPECTED_IMPORTS.jsonl' if target=='queryscan' else 'NGL_EXPECTED_IMPORTS.jsonl'
 files[name]=(E/name).read_text();sources+=[name]
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'selected_objects':{}},expected_time='Focused elaboration' if kind=='lean' else 'Optimized audit linker' if kind=='linkaudit' else 'Raw checked-kernel graph traversal')
if kind=='kani':cfg['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NGL_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NGL_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
if kind=='kani' and os.environ.get('NGL_PROGRAM'):
 cfg['root_package']='aspis-r1-cost-probe-program'
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NGL_src/programs/r1-cost-probe/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]='pool-adapter,private-leaf-salts'
if kind=='kani' and os.environ.get('NGL_CORE'):
 cfg['root_package']='aspis-core'
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NGL_src/crates/aspis-core/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]='r0'
if kind=='kani' and os.environ.get('NGL_STATEMENT'):
 fs=[r['features'] for r in json.loads((E/'NGL_K002-graph-check.json').read_text())['selected_closure'] if r['name']=='aspis-statement'][0]
 fs=[f for f in fs if f!='spend-dynamic-rate512'];cfg['root_package']='aspis-statement';cfg['metadata_features']=','.join('aspis-statement/'+f for f in fs)
 i=cfg['native_command'].index('--manifest-path');cfg['native_command'][i+1]=B+'/NGL_src/crates/aspis-statement/Cargo.toml'
 i=cfg['native_command'].index('--features');cfg['native_command'][i+1]=','.join(fs)
cfg['expected_time']='optimized compilation then scalar contract; no field multiplication' if kind=='kani' else 'optimized Charon frontend, then Aeneas emission; no arithmetic gate' if kind=='extract' else cfg['expected_time']
files[a+'.json']=json.dumps(cfg)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for directory in ['NGL_objects','NGL_tmp','NGL_native']:(b/directory).mkdir(parents=True,exist_ok=True)
(b/'NGL_objects'/{(target.replace('.','/')+'.olean')!r}).parent.mkdir(parents=True,exist_ok=True)
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
for module in (['NGL_STAGE2_IMPORT' if x['module']=='NGL_Stage2Driver' else 'NGL_COMBINED_IMPORT'] if x['kind'] in ['auditbatch','deltaaudit'] else [])+(['NEP_Planted','NEP_Mutations'] if x['module'] in ['NGL_Driver','NGL_ProofDriver','NGL_Stage2Driver','fixtures'] else [])+(['NGL_QueryModel'] if x['kind']=='auditbin' and x['module'].startswith('query') else [])+(['NGL_COMBINED_IMPORT'] if x['kind']=='auditbin' and (x['module'].startswith('proof') or x['module']=='scan') else [])+[n for line in ((b/x['sources'][0]).read_text().splitlines() if str(x['sources'][0]).endswith('.lean') else []) if line.startswith('import ') for n in line[7:].split() if n!='all'] if x['kind'] not in ['linkaudit','kani','extract','pins','review'] else []:
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
names += [str(p.relative_to(b)) for p in b.glob(a+'-graph*')]+[str(p.relative_to(b)) for p in b.glob(a+'-source*')]+[str(p.relative_to(b)) for p in b.glob(a+'-lock*')]+[str(p.relative_to(b)) for p in b.glob(a+'-erasure*')] if {kind!r}=='kani' else []
if {kind!r}=='deltaaudit':
 names += [str(p.relative_to(b)) for p in (b/'NGL_delta_audit').rglob('*') if p.is_file()]
 names += [str(p.relative_to(b)) for p in b.glob('NEP_proof7_*_REACHABLE.txt')]
if {kind!r}=='review':
 names += [str(p.relative_to(b)) for p in (b/'NGL_review_results').glob('*.json')]
 review=b/'NGL_review/evidence/slice-d-entry-20261105'
 for name in ['NGL_NATIVE_REVIEW.json','NGL_AUDIT.json','NGL_SOURCE_REVIEW.json','NGL_CLOSED.json','NGL_CANDIDATES.json','NGL_LEDGER_DELTA.json','NGL_EXPORTS.json','NGL_RESOURCE_FINAL.json','NGL_VALIDATION_FINAL.json']:
  if (review/name).exists():names += [str((review/name).relative_to(b))]
if {kind!r}=='pins':names += ['NGL_TOOL_PINS.json']
if {kind!r}=='extract':names += [a+'-extraction-pins.json',a+'.llbc']+[str(p.relative_to(b)) for p in (b/'NGL_extracted'/{target!r}).rglob('*') if p.is_file()]
names += [str(p.relative_to(b)) for p in b.glob('NEP_*_REACHABLE.txt')] if {kind!r}=='auditbatch' else [str(p.relative_to(b)) for p in b.glob('NEP_'+{target!r}+'_*_REACHABLE.txt')] if {kind!r}=='auditbin' else []
if {kind!r}=='auditbatch':names += [str(p.relative_to(b)) for p in (b/('NGL_stage2_audit' if {target!r}=='NGL_Stage2Driver' else 'NGL_final_audit')).rglob('*') if p.is_file()]
if {target!r} in ['scan','queryscan']:names+=['NGL_QUERY_LOADED_scan.jsonl' if {target!r}=='queryscan' else 'NGL_LOADED_scan.jsonl']
out={{n:(b/n).read_text() for n in names}}
for name in ['NGL_Driver','NGL_ProofDriver','NGL_Stage2Driver']:
 p=b/'NGL_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,t in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
if kind=='review':
 for n,t in out.items():
  if n.startswith('NGL_review/evidence/slice-d-entry-20261105/'):(E/n.split('/')[-1]).write_text(t)
# Archive raw graphs immediately; keep their uncompressed hashes for replay.
if kind in ['auditbin','auditbatch','deltaaudit']:
 import lzma
 for name in out:
  if name.startswith('NEP_') and name.endswith('_REACHABLE.txt'):
   p=E/name;data=p.read_bytes();(E/(name+'.sha256')).write_text(hashlib.sha256(data).hexdigest()+'  '+name+'\n')
   (E/(name+'.xz')).write_bytes(lzma.compress(data,preset=6));p.unlink()
assert a+'/receipt.json' in out,'Missing receipt; no resubmit'
rc=json.loads(out[a+'/receipt.json'])
with (E/'NGL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print('\n'.join(l for l in out[a+'/stdout.log'].splitlines() if l.startswith(('error:', 'VERIFICATION', ' ** ', 'Verification Time:', 'Manual Harness', 'Complete -', "'")))[-2000:]);sys.exit(rc['exit_status'])
