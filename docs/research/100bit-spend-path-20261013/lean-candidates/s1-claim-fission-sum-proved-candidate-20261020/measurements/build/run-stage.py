from pathlib import Path
import subprocess,shutil,hashlib,json,time,re,os
W=Path(__file__).resolve().parent;H=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020');E=W/'evidence';E.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
CG=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().removeprefix('0::').lstrip('/')
limits={x:(CG/x).read_text().strip() for x in ['memory.high','memory.max','memory.swap.max']};assert limits=={'memory.high':str(2*1024**3),'memory.max':str(4*1024**3),'memory.swap.max':'0'}
base=json.loads((W/'baseline-source-hashes.json').read_text())
for name,h in base['files'].items():assert sha(H/'src'/name)==h,name
assert not (W/'src').exists() and not (W/'sbf-target-verifier').exists()
start=time.monotonic();shutil.copytree(H/'src',W/'src',symlinks=True,ignore=shutil.ignore_patterns('.git','target'))
subprocess.run(['cp','-a','--reflink=auto',str(H/'sbf-target-verifier'),str(W/'sbf-target-verifier')],check=True,timeout=60)
pins=json.loads((W/'candidate-source-pins.json').read_text());cut=next(c for c in pins['cuts'] if c['path'].endswith('weights.rs'));p=W/'src'/cut['path'];old=p.read_bytes();assert hashlib.sha256(old).hexdigest()==cut['file_sha256'];oldspan=old[cut['start_byte']:cut['end_byte_exclusive']]
assert hashlib.sha256(oldspan).hexdigest()==cut['sha256'];new=old[:cut['start_byte']]+pins['candidate_transform']['after'].encode()+old[cut['end_byte_exclusive']:];p.write_bytes(new)
claim_transform=json.loads((W/'claim-transform.json').read_text());vp=W/'src/crates/aspis-r1-cost-probe/src/verifier.rs';vb=vp.read_text();assert vb.count(claim_transform['before'])==1;vp.write_text(vb.replace(claim_transform['before'],claim_transform['after']))
changes={}
for name,h in base['files'].items():
 current=sha(W/'src'/name)
 if current!=h:changes[name]={'before':h,'after':current}
assert set(changes)=={cut['path'],'crates/aspis-r1-cost-probe/src/verifier.rs'},changes
out=W/'artifacts';out.mkdir();env=dict(os.environ);env.update(CARGO_TARGET_DIR=str(W/'sbf-target-verifier'),CARGO_NET_OFFLINE='true',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin')
for k in ['RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']:env.pop(k,None)
cmd=['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(W/'src/programs/r1-cost-probe/Cargo.toml'),'--sbf-out-dir',str(out),'--features','pool-adapter,private-leaf-salts','--skip-tools-install','--offline','-j','4','--','--locked']
(E/'preflight.json').write_text(json.dumps({'baseline_revision':base['source_revision'],'baseline_verifier_sha256':sha(H/'artifacts/default/aspis_r1_cost_probe_program.so'),'changed_files':changes,'cache_seed':str(H/'sbf-target-verifier'),'limits':limits,'time_expected':'Source/cache copy then incremental optimized SBF build only; no proof generation or elimination','command':cmd,'preparation_seconds':time.monotonic()-start},indent=2)+'\n')
(E/'command.json').write_text(json.dumps(cmd,indent=2)+'\n');before=(CG/'memory.events').read_text();start=time.monotonic()
with (E/'build.log').open('w') as log:result=subprocess.run(['/usr/bin/time','-v','-o',str(E/'time.log'),*cmd],cwd=W/'src',env=env,stdout=log,stderr=subprocess.STDOUT,timeout=180)
txt=(E/'time.log').read_text();m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',txt)
rec={'exit_status':result.returncode,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(m[1]) if m else None,'scope_memory_peak_bytes':int((CG/'memory.peak').read_text()),'scope_swap_peak_bytes':int((CG/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(CG/'memory.events').read_text(),'classification':'CANDIDATE NOT ADOPTED; frozen/live workspaces unchanged'}
if result.returncode==0:
 so=out/'aspis_r1_cost_probe_program.so';rec['artifact_sha256']=sha(so);rec['artifact_bytes']=so.stat().st_size;rec['baseline_byte_identical']=so.read_bytes()==(H/'artifacts/default/aspis_r1_cost_probe_program.so').read_bytes()
(E/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
if result.returncode:print((E/'build.log').read_text()[-4000:])
raise SystemExit(result.returncode)
