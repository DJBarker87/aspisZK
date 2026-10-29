"""New finite controls: actual deployed rlibs/std with failed stderr writes."""
from pathlib import Path
import subprocess,json,hashlib,os
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');T=D.parent/'codex-pv-rdea-20261028/client-target/release/deps'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rustc=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc');src=D/'PV_DIAG2_ErrorExit.rs';anyhow=next(T.glob('libanyhow-*.rlib'));aspis=next(T.glob('libaspis_r1_cost_probe-*.rlib'));exe=D/'error-write-failures'
cmd=[str(rustc),'--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','--extern','anyhow='+str(anyhow),'--extern','aspis_r1_cost_probe='+str(aspis),'-L','dependency='+str(T),str(src),'-o',str(exe)]
print('Expected time: optimized probe compilation, then 24 failed-stderr controls; no heavy arithmetic',flush=True)
subprocess.run(cmd,check=True);env=dict(os.environ,RUST_BACKTRACE='0',RUST_LIB_BACKTRACE='0');rows=[]
for mode in ['closed','full']:
 for n in range(12):
  def close_stderr():os.close(2)
  with open('/dev/full','wb') as full:
   r=subprocess.run([str(exe),str(n)],env=env,stdout=subprocess.PIPE,stderr=full if mode=='full' else subprocess.DEVNULL,preexec_fn=close_stderr if mode=='closed' else None)
  assert r.returncode==(0 if n==11 else 1) and r.stdout==b''
  rows.append(dict(mode=mode,variant=n,exit=r.returncode,stdout_hex=r.stdout.hex()))
record=dict(classification='finite native validation, public unit-error controls; not honest proving runs or universal failure independence',command=cmd,toolchain=subprocess.check_output([str(rustc),'-vV'],text=True),source_sha256=sha(src),rlibs={str(p):sha(p) for p in [anyhow,aspis]},binary_sha256=sha(exe),features='exact deployed rlibs; inherited resolved-build-units.json',rows=rows)
(D/'error-write-failures.json').write_text(json.dumps(record,indent=2)+'\n');print('passed',len(rows),'new failed-stderr controls')
