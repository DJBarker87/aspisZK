#!/usr/bin/env python3
import os,sys,json,subprocess,time,hashlib
from pathlib import Path
D=Path('/home/dombarker/project-offloads/codex-pv-mf-20261029')
S=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
if len(sys.argv)==1:
 barrier='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
 with (D/'native02-admission.log').open('a') as f:r=subprocess.run(['python3',barrier,str(D/'native02-admission.json')],stdout=f,stderr=subprocess.STDOUT)
 if r.returncode:sys.exit(r.returncode)
 if json.loads((D/'native02-admission.json').read_text()).get('allowed') is not True:sys.exit(78)
 sys.exit(subprocess.run(['systemd-run','--user','--scope','--unit=pv-mf-native02','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'PV_MF_native.py'),'inside']).returncode)
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().strip().split('::')[-1])
limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert list(limits.values())==['6442450944','8589934592','0','64']
checks=[]
for row in json.loads((D/'build-inputs.json').read_text()):
 p=S/row['path'];actual=sha(p) if p.is_file() else None
 checks.append(dict(row,actual=actual,matches=actual==row['sha256']))
(D/'host-input-check.json').write_text(json.dumps(checks,indent=2)+'\n')
assert all(r['matches'] for r in checks),'source mismatch: never compile different source'
env=os.environ.copy();env['PATH']='/home/dombarker/.cargo/bin:'+env.get('PATH','');env.update(RUSTUP_TOOLCHAIN='1.94.1',RUSTC_BOOTSTRAP='1',CARGO_TARGET_DIR=str(D/'target'),RUSTC_WRAPPER='/home/dombarker/project-offloads/codex-pv-rdea-20261028/emit-wrapper.py')
(D/'environment.json').write_text(json.dumps({k:v for k,v in env.items() if k.startswith(('RUST','CARGO','CC','CFLAGS','LDFLAGS'))},indent=2)+'\n')
(D/'toolchain.txt').write_text(subprocess.check_output(['rustc','-Vv'],env=env,text=True))
cmd=['taskset','--cpu-list','0-3','cargo','build','--release','--offline','--locked','--manifest-path',str(S/'tools/r1-cost-probe/Cargo.toml'),'-p','aspis-r1-cu-probe','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','devnet_spend','-j','4']
t=time.monotonic()
with (D/'native02-output.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(D/'native02-time.log'),*cmd],env=env,cwd=S,stdout=f,stderr=subprocess.STDOUT)
artifacts=[]
for name,p,expected in [('client',str(D/'target/release/devnet_spend'),'fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348')]+[(x['name'],x['path'],x['sha256']) for x in json.loads((D/'elf-inputs.json').read_text())]:
 path=Path(p);actual=sha(path) if path.is_file() else None
 artifacts.append(dict(name=name,path=p,expected=expected,sha256=actual,bytes=path.stat().st_size if path.is_file() else None,matches=actual==expected))
(D/'artifacts.json').write_text(json.dumps(artifacts,indent=2)+'\n')
rec=dict(target='V346 reproducible devnet_spend release build and three pinned ELF hashes',command=cmd,exit=r.returncode,wall_seconds=time.monotonic()-t,limits=limits,peak_cgroup_bytes=(cg/'memory.peak').read_text().strip(),swap_current_bytes=(cg/'memory.swap.current').read_text().strip(),source_revision='85addf5a9764aa5e17d28bd6cf96bbda084447c5',print_axioms='N/A: no Lean invocation',phase='compilation only',launcher_sha256=sha(__file__))
(D/'native02-receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));sys.exit(r.returncode)
