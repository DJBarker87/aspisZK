from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,time
W=Path(__file__).resolve().parent
cfg=json.loads((W/'config.json').read_text())
assert sys.argv[1]=='devnet-build'
G=1024**3
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().removeprefix('0::').lstrip('/')
limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
assert limits=={'memory.high':str(2*G),'memory.max':str(4*G),'memory.swap.max':'0'},limits
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
root=Path('/home/dombarker/project-offloads/s4-combined-candidate-20261021/work')
source=root/'src'
expected={
 'crates/aspis-r1-cost-probe/src/fast_dots.rs':'53fa714e84ded64b844061f4d1b66ad20ee1ba48c3873a73970f80ede8a0b602',
 'crates/aspis-r1-cost-probe/src/fast_pairing.rs':'2cb96261cecfd766b5e1b45a585b74c5f59c20c6be4f41e806239e2786ca7313',
 'crates/aspis-r1-cost-probe/src/weights.rs':'28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137'
}
for rel,h in expected.items(): assert sha(source/rel)==h,(rel,sha(source/rel),h)
default=root/'artifacts/aspis_r1_cost_probe_program.so'
assert sha(default)=='40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0'
T=W/'identity-task'; ad=T/'artifacts/default'; dv=T/'artifacts/devnet';
assert not T.exists()
ad.mkdir(parents=True);dv.mkdir(parents=True)
shutil.copy2(default,ad/'aspis_r1_cost_probe_program.so')
shutil.copy2(W/'r1-devnet.template.json',T/'r1-devnet.template.json')
template=json.loads((T/'r1-devnet.template.json').read_text())
env=dict(os.environ);env['CARGO_TARGET_DIR']=str(root/'sbf-target-verifier');env['CARGO_NET_OFFLINE']='true';env['RUSTFLAGS']='-C link-arg=-Wl,--threads=4';env['CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS']='-C link-arg=--threads=4';env['PATH']='/home/dombarker/.cargo/bin:/usr/bin:/bin';env['ASPIS_R1_POOL_PROGRAM_ID']=template['programs']['pool'];env['ASPIS_R1_REGISTRY_PROGRAM_ID']=template['programs']['registry']
for k in ('CARGO_ENCODED_RUSTFLAGS',):env.pop(k,None)
cmd=['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(source/'programs/r1-cost-probe/Cargo.toml'),'--sbf-out-dir',str(dv),'--features','pool-adapter,private-leaf-salts','--skip-tools-install','--offline','-j','4','--','--locked']
run=W/'devnet-build';run.mkdir()
(run/'preflight.json').write_text(json.dumps({'candidate_source_hashes':expected,'default_artifact_sha256':sha(default),'default_artifact_bytes':default.stat().st_size,'template':template,'candidate_root':str(root),'command':cmd,'environment':{'CARGO_TARGET_DIR':env['CARGO_TARGET_DIR'],'CARGO_NET_OFFLINE':env['CARGO_NET_OFFLINE'],'RUSTFLAGS':env['RUSTFLAGS'],'CARGO_TARGET_SBPF_SOLANA_RUSTFLAGS':env['CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS'],'pool':env['ASPIS_R1_POOL_PROGRAM_ID'],'registry':env['ASPIS_R1_REGISTRY_PROGRAM_ID']},'time_expected':'incremental optimized SBF compilation only, reusing candidate warm target cache; no proof generation'},indent=2)+'\n')
start=time.monotonic(); before=(cg/'memory.events').read_text();
with (run/'build.log').open('w') as log:
 try: res=subprocess.run(['/usr/bin/time','-v','-o',str(run/'time.log'),'env','-u','RUSTFLAGS',*cmd],cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600);status=res.returncode;timed=False
 except subprocess.TimeoutExpired: status=124;timed=True
elapsed=round(time.monotonic()-start,3)
if status==0:
 artifact=dv/'aspis_r1_cost_probe_program.so'
 shutil.copy2(root/'sbf-target-verifier/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so',dv/'linked.elf')
 timing=(run/'time.log').read_text();m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
 rec={'exit_status':status,'timed_out':timed,'wall_seconds':elapsed,'peak_process_rss_kib':int(m[1]) if m else None,'scope_peak_bytes':int((cg/'memory.peak').read_text()),'swap_current_bytes':int((cg/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'limits':limits,'source_hashes':expected,'default_artifact_sha256':sha(default),'devnet_artifact_sha256':sha(artifact),'devnet_artifact_bytes':artifact.stat().st_size,'command':cmd}
else:
 rec={'exit_status':status,'timed_out':timed,'wall_seconds':elapsed,'limits':limits,'source_hashes':expected,'command':cmd}
(run/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
if status: raise SystemExit(status)
identity=W/'identity.py'
identity_out=T/'receipts/identity';identity_out.parent.mkdir(parents=True)
cmd_id=['python3',str(identity),str(T)]
with (run/'identity.log').open('w') as log: ir=subprocess.run(cmd_id,cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=60)
rec['identity_exit_status']=ir.returncode;rec['identity_command']=cmd_id
if ir.returncode: raise SystemExit(ir.returncode)
(run/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({'exit_status':status,'wall_seconds':elapsed,'devnet_artifact_sha256':rec['devnet_artifact_sha256'],'identity_exit_status':ir.returncode}),flush=True)
