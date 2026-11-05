"""Private serial runner; uses unchanged admitted S2W launcher."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-event-native-20261106'
C='/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIC_20261106'
W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
H='dombarker@100.108.41.90';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,kind,target=sys.argv[1:];assert (a.startswith('NIC_L') and 1<=int(a[-3:])<=60) or (a.startswith('NIC_K') and 1<=int(a[-3:])<=80)
assert not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NIC_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
paths=json.loads((E/'NIC_PATHS.json').read_text())
env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NIC_tmp',LEAN_PATH=':'.join(paths))
files={};sources=[]
if kind=='kani':
 for n in ['NIC_gate.py','NIC_graph.py','NIC_build.py','NIC_native.rs.txt','NIC_opening.rs.txt','NIC_purity.rs.txt','NIC_transcript.rs.txt','NIC_dots.rs.txt']:files[n]=(E/n).read_text()
 files['NIC_KMX.patch']=(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text();sources=list(files);command=['python3','NIC_gate.py',a+'.json',target]
 env.update(CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1')
 native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NIC_src/programs/r1-cost-probe/Cargo.toml','--target-dir',B+'/NIC_target','--lib','--features','pool-adapter,private-leaf-salts','-j','1','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--exact','--harness','NIC_purity::'+target,'--output-format','terse']
 cfg_native=native
elif kind=='lean':
 n='NIC_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NIC_generated','-o','NIC_objects/'+target+'.olean',n]
 if target in ['NIC_Driver','NIC_ProofDriver','NIC_Scanner','NFA_WALKER','NFA_MemoryLimit']:command+=['-c','NIC_native/'+target+'.c']
elif kind=='linkaudit':
 sources=['NIC_native/'+target+'.c','NIC_native/NFA_WALKER.c','NIC_native/NFA_MemoryLimit.c']
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NIC_native/'+target,*sources]
elif kind=='auditbin':
 sources=['NIC_generated/'+('NIC_Scanner' if target=='scan' else 'NIC_Driver')+'.lean'];command=['NIC_native/'+('NIC_Scanner' if target=='scan' else 'NIC_Driver'),target]
else:raise ValueError(kind)
if target=='scan':
 files['NIC_EXPECTED_IMPORTS.jsonl']=(E/'NIC_EXPECTED_IMPORTS.jsonl').read_text();sources+=['NIC_EXPECTED_IMPORTS.jsonl']
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'selected_objects':{}},expected_time='Optimized frozen-body compilation then named CBMC verification; multiplication excluded' if kind=='kani' else 'Focused elaboration' if kind=='lean' else 'Optimized audit linker' if kind=='linkaudit' else 'Raw checked-kernel graph traversal')

if kind=='kani':cfg['native_command']=cfg_native
files[a+'.json']=json.dumps(cfg)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({json.dumps(files)!r})
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
for module in (['NEP_Planted','NEP_Mutations'] if x['module'] in ['NIC_Driver','NIC_ProofDriver','fixtures'] else [])+(['NIC_CombinedFinal'] if x['kind']=='auditbin' and (x['module'].startswith('proof') or x['module']=='scan') else [])+[n for line in (b/x['sources'][0]).read_text().splitlines() if line.startswith('import ') for n in line[7:].split() if n!='all'] if x['kind'] not in ['linkaudit','kani'] else []:
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
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']+[str(p.relative_to(b)) for p in b.glob(a+'-*.json')]
names += [str(p.relative_to(b)) for p in b.glob('NEP_'+{target!r}+'_*_REACHABLE.txt')] if {kind!r}=='auditbin' else []
if {target!r}=='scan':names+=['NIC_LOADED_scan.jsonl']
names += ['NIC_harness.patch'] if {kind!r}=='kani' else []
out={{n:(b/n).read_text() for n in names}}
for name in ['NIC_Driver','NIC_ProofDriver','NIC_Scanner']:
 p=b/'NIC_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,t in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
# Archive raw graphs immediately; keep their uncompressed hashes for replay.
if kind=='auditbin':
 import lzma
 for name in out:
  if name.startswith('NEP_') and name.endswith('_REACHABLE.txt'):
   p=E/name;data=p.read_bytes();(E/(name+'.sha256')).write_text(hashlib.sha256(data).hexdigest()+'  '+name+'\n')
   (E/(name+'.xz')).write_bytes(lzma.compress(data,preset=6));p.unlink()
assert a+'/receipt.json' in out,'Missing receipt; no resubmit'
rc=json.loads(out[a+'/receipt.json'])
with (E/'NIC_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(out[a+'/stdout.log'][-1500:]);sys.exit(rc['exit_status'])
