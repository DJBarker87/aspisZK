from pathlib import Path
import subprocess,json,hashlib,os
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');B=D.parent/'codex-pv-rdea-20261028';T=B/'client-target/release/deps'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=D/'PV_DIAG2_ErrorExit.rs';plan=D.parent/'codex-pv-fscan-20261028/src/tools/r1-cost-probe/src/bin/devnet_spend/plan.rs'
body='fn err(e:impl std::fmt::Debug)->anyhow::Error{anyhow!("{e:?}")}'
assert body in source.read_text() and body in plan.read_text()
rustc=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc')
anyhow=next(T.glob('libanyhow-*.rlib'));aspis=next(T.glob('libaspis_r1_cost_probe-*.rlib'))
cmd=[str(rustc),'--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','--extern','anyhow='+str(anyhow),'--extern','aspis_r1_cost_probe='+str(aspis),'-L','dependency='+str(T),str(source),'-o',str(D/'error-exit')]
print('phase: optimized compilation of diagnostic probe, then finite unit-variant controls; no proof generation',flush=True)
subprocess.run(cmd,check=True)
names=['Parse','Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation','Rejected','AttemptsExhausted','Entropy'];rows=[]
settings=[{}, {'RUST_BACKTRACE':'0'}, {'RUST_BACKTRACE':'1'}, {'RUST_BACKTRACE':'1','RUST_LIB_BACKTRACE':'0'}, {'RUST_BACKTRACE':'0','RUST_LIB_BACKTRACE':'1'}]
for setting in settings:
 env={k:v for k,v in os.environ.items() if k not in ['RUST_BACKTRACE','RUST_LIB_BACKTRACE']};env.update(setting)
 for n in range(12):
  r=subprocess.run([str(D/'error-exit'),str(n)],env=env,capture_output=True,text=True)
  expected='' if n==11 else 'Error: '+names[n]+'\n'
  enabled=setting.get('RUST_LIB_BACKTRACE',setting.get('RUST_BACKTRACE','0'))!='0'
  assert r.returncode==(0 if n==11 else 1) and r.stdout==''
  if n!=11:
   assert r.stderr.startswith(expected)
   assert ('Stack backtrace:' in r.stderr)==enabled
   if not enabled:assert r.stderr==expected
  else:assert r.stderr==''
  rows.append(dict(variant='success' if n==11 else names[n],environment=setting,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,stderr_sha256=hashlib.sha256(r.stderr.encode()).hexdigest()))
pins=dict(command=cmd,source_sha256=sha(source),native_plan_sha256=sha(plan),exact_body=body,rlibs={str(p):sha(p) for p in [anyhow,aspis]},toolchain=subprocess.check_output([str(rustc),'-vV'],text=True),profile='release opt3, overflow/debug assertions off, panic unwind',features_record='inherited resolved-build-units.json; exact deployed rlibs reused',classification='finite native controls of actual Error Debug, exact plan::err body, anyhow and std Termination; no whole-run source refinement',rows=rows)
(D/'error-exit-validation.json').write_text(json.dumps(pins,indent=2)+'\n')
print('passed',len(rows),'controls')
