from pathlib import Path
import subprocess,os,json,sys,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
who,label,*cmd=sys.argv[1:];W=H/"candidate";out=W/label;out.mkdir(exist_ok=False)
pre=subprocess.run(['python3',str(H/'reservation.py'),str(out/'reservation.json')],stdout=open(out/'reservation.log','w'),stderr=subprocess.STDOUT);
if pre.returncode != 0 or json.loads((out/'reservation.json').read_text()).get('allowed') is not True:sys.exit(78)
(W/'capped.py').write_text((H/'capped-template.py').read_text().replace('/home/dombarker/project-offloads/codex-cx-pin-20261020/source-revision.txt',str(W/'source-revision.txt')))
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(Path('/home/dombarker/project-offloads/codex-pv-rebase-20261026/native-target')),RUSTFLAGS='-C link-arg=-Wl,--threads=4')
(out/'command.json').write_text(json.dumps(dict(command=cmd,source_revision=(W/'source-revision.txt').read_text().strip(),env={k:env[k] for k in ['PATH','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','RUSTFLAGS']},expected_time='optimized compilation' if cmd[0]=='cargo' else 'optimized complete retry-owner proof generation and P_R1 elimination'),indent=2)+'\n')
run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py',str(out/'admission-barrier.json'),'python3',str(W/'capped.py'),str(out/'receipt'),'optimized compilation' if cmd[0]=='cargo' else 'optimized complete retry-owner proof generation and P_R1 elimination','--',*cmd]
with (out/'scope.log').open('w') as log:
 status=subprocess.run(run,cwd=W/'src',env=env,stdout=log,stderr=subprocess.STDOUT).returncode
barrier=out/'admission-barrier.json'
if barrier.exists() and json.loads(barrier.read_text()).get('allowed') is not True:
 (out/'refusal-classification.json').write_text(json.dumps(dict(raw_exit=status,classified_exit=78,reason='reservation barrier refused; no command ran'))+'\n')
 sys.exit(78)
if status:sys.exit(status)
if cmd[0]=='cargo':
 (W/'bin').mkdir(exist_ok=True)
 for name in [cmd[cmd.index('--example')+1]]:
  src=Path('/home/dombarker/project-offloads/codex-pv-rebase-20261026/native-target/release/examples')/name;dst=W/'bin'/name
  assert src.exists(),src
  import shutil
  shutil.copy2(src,dst)
 (out/'binary-pins.json').write_text(json.dumps({p.name:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in (W/'bin').iterdir()},indent=2)+'\n')
