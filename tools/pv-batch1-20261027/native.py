from pathlib import Path
import subprocess,os,json,sys,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch1-20261027')
who,label,*cmd=sys.argv[1:];W=H/who;out=W/label;out.mkdir(exist_ok=False)
with (out/'reservation.json').open('w') as log:
 pre=subprocess.run(['python3',str(H/'Port13GATE_admission.py')],stdout=log,stderr=subprocess.STDOUT)
assert pre.returncode==0,pre.returncode
(W/'capped.py').write_text((H/'capped-template.py').read_text().replace('/home/dombarker/project-offloads/codex-cx-pin-20261020/source-revision.txt',str(W/'source-revision.txt')))
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'native-target'),RUSTFLAGS='-C link-arg=-Wl,--threads=4')
toolchain=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','-Vv'],text=True,cwd=W/'src')
assert toolchain.startswith('rustc 1.94.1 '),toolchain
note='optimized compilation' if cmd[0]=='cargo' else ('static symbol/call extraction from the built binary' if any('binary-route.py' in x for x in cmd) else 'optimized complete retry-owner proof generation and P_R1 elimination')
(out/'command.json').write_text(json.dumps(dict(command=cmd,toolchain=toolchain,source_revision=(W/'source-revision.txt').read_text().strip(),env={k:env[k] for k in ['PATH','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','RUSTFLAGS']},expected_time=note),indent=2)+'\n')
run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(W/'capped.py'),str(out/'receipt'),note,'--',*cmd]
status=subprocess.run(run,cwd=W/'src',env=env).returncode
if status:sys.exit(status)
if cmd[0]=='cargo':
 (W/'bin').mkdir(exist_ok=True)
 for name in [cmd[cmd.index('--example')+1] if '--example' in cmd else cmd[cmd.index('--bin')+1]]:
  src=H/('native-target/release/examples' if '--example' in cmd else 'native-target/release')/name;dst=W/'bin'/name
  if src.exists():
   import shutil
   shutil.copy2(src,dst)
 (out/'binary-pins.json').write_text(json.dumps({p.name:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in (W/'bin').iterdir()},indent=2)+'\n')
