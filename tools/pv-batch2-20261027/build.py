from pathlib import Path
import os,subprocess,json,sys,hashlib,time
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
who,mode,label=sys.argv[1:]; W=H/"candidate";out=W/label;out.mkdir(exist_ok=False)
rev=(W/'source-revision.txt').read_text().strip()
# Reuse the existing receipt runner with this snapshot's source pin.
runner=W/'capped.py'
runner.write_text((H/'capped-template.py').read_text().replace('/home/dombarker/project-offloads/codex-cx-pin-20261020/source-revision.txt',str(W/'source-revision.txt')))
target=Path('/home/dombarker/project-offloads/codex-pv-rebase-20261026')/('sbf-target-pool' if mode=='pool' else 'sbf-target-verifier')
if not target.exists():subprocess.run(['cp','-a','--reflink=auto',str(H.parent/'codex-cx-lowering2-20261026'/target.name),str(target)],check=True)
for p in (W/'src').glob('**/*.rs'):os.utime(p,None)
pre=subprocess.run(['python3',str(H/'reservation.py'),str(out/'reservation.json')],stdout=open(out/'reservation.log','w'),stderr=subprocess.STDOUT);
if pre.returncode != 0 or json.loads((out/'reservation.json').read_text()).get('allowed') is not True:sys.exit(78)
manifest='programs/aspis-pool' if mode=='pool' else 'programs/r1-cost-probe'
features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if mode=='pool' else 'pool-adapter,private-leaf-salts'
cmd=['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(W/'src'/manifest/'Cargo.toml'),'--sbf-out-dir',str(out/'artifacts'),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_HOME='/home/dombarker/.cargo',CARGO_TARGET_DIR=str(target),CARGO_NET_OFFLINE='true',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4',RUSTC_WRAPPER=str(H/'rustc-diagnostics.py'),S10_DIAGNOSTICS=str(out/'diagnostics'))
for key in ['RUSTFLAGS','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']:env.pop(key,None)
if mode=='devnet':
 ids=json.loads((H/'r1-devnet.template.json').read_text())['programs'];env.update(ASPIS_R1_POOL_PROGRAM_ID=ids['pool'],ASPIS_R1_REGISTRY_PROGRAM_ID=ids['registry'])
(out/'command.json').write_text(json.dumps(dict(command=cmd,source_revision=rev,env={k:v for k,v in env.items() if k.startswith(('CARGO_','ASPIS_','S10_','RUST'))},precedent='evidence/lowering2-20261026/Low2_build_host.py'),indent=2)+'\n')
run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py',str(out/'admission-barrier.json'),'python3',str(runner),str(out/'receipt'),'optimized SBF compilation and diagnostic emission','--','timeout','600',*cmd]
with (out/'scope.log').open('w') as log:
 status=subprocess.run(run,cwd=W/'src',env=env,stdout=log,stderr=subprocess.STDOUT).returncode
barrier=out/'admission-barrier.json'
if barrier.exists() and json.loads(barrier.read_text()).get('allowed') is not True:
 (out/'refusal-classification.json').write_text(json.dumps(dict(raw_exit=status,classified_exit=78,reason='reservation barrier refused; no command ran'))+'\n')
 sys.exit(78)
if status:sys.exit(status)
a=out/'artifacts'/('aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so')
pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
r=dict(source_revision=rev,mode=mode,sha256=hashlib.sha256(a.read_bytes()).hexdigest(),bytes=a.stat().st_size,expected=pins[mode]);r['matches']=r['sha256']==r['expected']
(out/'comparison.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)


for key in (out/'artifacts').glob('*keypair.json'):key.chmod(0o600)
if not r["matches"]:sys.exit(2)
