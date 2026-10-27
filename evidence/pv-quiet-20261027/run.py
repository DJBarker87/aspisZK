from pathlib import Path
import os,sys,json,subprocess,time,hashlib,shutil
H=Path('/home/dombarker/project-offloads/codex-pv-quiet-20261027')
G=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy')
REVS={'control':'c57a344726745387efb38d1571d885c69ce829ee','candidate':'8873306db187ec0b530d2469d4ec0f7f85e25365'}
def run(label,who,cmd,owner=False):
 out=H/label;out.mkdir()
 env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/who/'target'),RUSTFLAGS='-C link-arg=-Wl,--threads=4',PV_REV=REVS[who])
 if owner:env['QUIET_WINDOW_OWNER']='1'
 (out/'command.json').write_text(json.dumps(dict(command=cmd,revision=REVS[who],env={k:v for k,v in env.items() if k.startswith(('CARGO','RUST','PV_','QUIET'))},expected_time='optimized compilation' if cmd[0]=='cargo' else 'optimized proof generation and P_R1 elimination'),indent=2))
 with (out/'reservation.log').open('w') as f:r=subprocess.run(['python3',str(G/'reservation.py'),str(out/'reservation.json')],stdout=f,stderr=subprocess.STDOUT,env=env)
 if r.returncode:return r.returncode
 command=['systemd-run','--user','--scope','--unit=pv-quiet-'+label,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G/'barrier.py'),str(out/'barrier.json'),'python3',str(H/'capped.py'),str(out/'receipt'), 'optimized compilation' if cmd[0]=='cargo' else 'optimized proof generation and P_R1 elimination','--',*cmd]
 with (out/'scope.log').open('w') as f:r=subprocess.run(command,cwd=H/who/'source',env=env,stdout=f,stderr=subprocess.STDOUT)
 if r.returncode and (out/'barrier.json').exists() and not (out/'receipt/receipt.json').exists():
  admission=json.loads((out/'barrier.json').read_text())
  if not admission['allowed']:
   (out/'refusal-classification.json').write_text(json.dumps(dict(raw_exit=r.returncode,classified_exit=78,reason='reservation barrier refused before command execution'),indent=2))
   return 78
 return r.returncode
if __name__=='__main__':
 who=sys.argv[1]
 cmd=['cargo','build','--release','--locked','--offline','-j','4','-p','aspis-r1-cost-probe','--features','optimized-terminal,r1p-check,ct-host-prover','--example','prover_rw_gate']
 code=run('build-'+who+('-'+sys.argv[2] if len(sys.argv)>2 else ''),who,cmd)
 if code==0:
  dest=H/who/'bin/prover_rw_gate';dest.parent.mkdir();shutil.copy2(H/who/'target/release/examples/prover_rw_gate',dest)
  (H/('pin-'+who+'.json')).write_text(json.dumps(dict(revision=REVS[who],sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),bytes=dest.stat().st_size),indent=2))
 sys.exit(code)
