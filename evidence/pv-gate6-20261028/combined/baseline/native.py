"""Job-local optimized runner; client builds run from pinned toolchain directory."""
from pathlib import Path
import subprocess,os,json,sys,hashlib,shutil
H=Path(__file__).resolve().parent
label,*cmd=sys.argv[1:];out=H/label;out.mkdir(exist_ok=False)
pre=subprocess.run(['python3',str(H/'reservation.py'),str(out/'reservation.json')],stdout=open(out/'reservation.log','w'),stderr=subprocess.STDOUT)
if pre.returncode or not json.loads((out/'reservation.json').read_text()).get('allowed',False):sys.exit(pre.returncode or 78)
isbuild=cmd[0]=='cargo';client=isbuild and '--bin' in cmd and 'devnet_spend' in cmd
cwd=H/'source/tools/r1-cost-probe' if client else H/'source'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'native-target'),RUSTFLAGS='-C link-arg=-Wl,--threads=4')
compiler=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','-vV'],text=True,cwd=cwd,env=env)
assert compiler.startswith('rustc 1.94.1 '),compiler
(out/'rustc-vV.txt').write_text(compiler)
note='optimized compilation' if isbuild else 'optimized complete retry-owner proof generation and P_R1 elimination'
(out/'command.json').write_text(json.dumps(dict(command=cmd,cwd=str(cwd),source_revision=(H/'source-revision.txt').read_text().strip(),env={k:env[k] for k in ['PATH','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','RUSTFLAGS']},expected_time=note),indent=2)+'\n')
barrier='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py'
run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',barrier,str(out/'admission-barrier.json'),'python3',str(H/'capped.py'),str(out/'receipt'),note,'--',*(['taskset','--cpu-list','0-3',*cmd] if isbuild else cmd)]
status=subprocess.run(run,cwd=cwd,env=env).returncode
if status:sys.exit(status)
if isbuild:
 name=cmd[cmd.index('--example')+1] if '--example' in cmd else cmd[cmd.index('--bin')+1]
 src=H/'native-target/release'/('examples/'+name if '--example' in cmd else name)
 (H/'bin').mkdir(exist_ok=True);shutil.copy2(src,H/'bin'/name)
 (out/'binary-pins.json').write_text(json.dumps({p.name:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in (H/'bin').iterdir()},indent=2)+'\n')
