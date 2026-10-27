from pathlib import Path
import subprocess,os,json,sys,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298')
who,label,*cmd=sys.argv[1:];W=H;out=W/label;out.mkdir(exist_ok=False)
pre=subprocess.run(['python3',str(H/'reservation.py'),str(out/'reservation.json')],stdout=open(out/'reservation.log','w'),stderr=subprocess.STDOUT);
if pre.returncode or not json.loads((out/'reservation.json').read_text()).get('allowed',False):sys.exit(pre.returncode or 78)
(W/'capped.py').write_text((H/'capped-template.py').read_text().replace('/home/dombarker/project-offloads/codex-cx-pin-20261020/source-revision.txt',str(H/'source-revision.txt')))
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(Path('/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298/native-target')),RUSTFLAGS='-C link-arg=-Wl,--threads=4')
toolchain=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','-Vv'],text=True,cwd=W/'source');assert toolchain.startswith('rustc 1.94.1 '),toolchain
(out/'toolchain.txt').write_text(toolchain)
note='optimized compilation' if cmd[0]=='cargo' else ('static symbol and call extraction' if any('binary-route.py' in a for a in cmd) else 'optimized complete retry-owner proof generation and P_R1 elimination')
(out/'command.json').write_text(json.dumps(dict(command=cmd,source_revision=(W/'source-revision.txt').read_text().strip(),env={k:env[k] for k in ['PATH','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','RUSTFLAGS']},expected_time=note),indent=2)+'\n')
run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py',str(out/'admission-barrier.json'),'python3',str(W/'capped.py'),str(out/'receipt'),note,'--',*(['taskset','--cpu-list','0-3',*cmd] if cmd[0]=='cargo' else cmd)]
status=subprocess.run(run,cwd=W/'source',env=env).returncode
if status:sys.exit(status)
if cmd[0]=='cargo':
 (W/'bin').mkdir(exist_ok=True)
 for name in [cmd[cmd.index('--example')+1] if '--example' in cmd else cmd[cmd.index('--bin')+1]]:
  src=(H/'native-target/release/examples' if '--example' in cmd else H/'native-target/release')/name;dst=W/'bin'/name
  assert src.exists(),src
  import shutil
  shutil.copy2(src,dst)
 (out/'binary-pins.json').write_text(json.dumps({p.name:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in (W/'bin').iterdir()},indent=2)+'\n')
