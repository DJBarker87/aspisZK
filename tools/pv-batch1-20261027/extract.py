"""Extract exact applied leaf bodies; no extractor/backend modifications."""
from pathlib import Path
import subprocess,os,json,hashlib,sys
H=Path('/home/dombarker/project-offloads/codex-pv-batch1-20261027')
X=H.parent/'codex-pv-extract-20261027'; PIN=H.parent/'codex-pv-cb-20261026/pinned-tools/aeneas'
expected={'charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','aeneas':'562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'}
assert hashlib.sha256((X/'charon').read_bytes()).hexdigest()==expected['charon']
assert hashlib.sha256(PIN.read_bytes()).hexdigest()==expected['aeneas']

def function(s,name):
 i=s.index('fn '+name); start=s.rfind('\n',0,i)+1
 j=s.index('{',i);level=1;k=j+1
 while level:
  if s[k]=='{':level+=1
  elif s[k]=='}':level-=1
  k+=1
 return s[start:k]+'\n'

def run(label,cmd,cwd):
 o=H/label;o.mkdir(exist_ok=False)
 with (o/'reservation.json').open('w') as log:
  r=subprocess.run(['python3',str(H/'Port13GATE_admission.py')],stdout=log,stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(78)
 (o/'command.json').write_text(json.dumps(dict(command=cmd,source_revision=(H/'candidate/source-revision.txt').read_text().strip(),preflight=True,pins=expected),indent=2))
 runner=H/'candidate/capped.py'
 with (o/'launcher.log').open('w') as log:
  r=subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(runner),str(o/'receipt'),'optimized MIR compilation and symbolic extraction; no elimination','--',*cmd],cwd=cwd,stdout=log,stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(r.returncode)

op=int(sys.argv[1]);suffix=sys.argv[2]
file,name={230:('prover_helper_sum.rs','state_only_copy_helper_sum'),254:('prover_powers.rs','powers'),258:('ct_pole.rs','all_slots_clear')}[op]
src=H/'candidate/src/crates/aspis-r1-cost-probe/src'/file;s=src.read_text()
code='use aspis_core::field::{QM31, WideExact as E};\n'
if op==230: code+='const TRACE_ROWS:usize=1024;\n'+function(s,name)
if op==254: code+=function(s,name)
if op==258: code+=function(s,'equal')+function(s,'keep_clear')+function(s,name)
p=H/'probes'/str(op);p.mkdir(parents=True,exist_ok=True)
(p/'lib.rs').write_text(code)
(p/'source-binding.json').write_text(json.dumps(dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),body=name,verbatim_body=True,probe_sha256=hashlib.sha256(code.encode()).hexdigest()),indent=2))
(p/'Cargo.toml').write_text('[package]\nname="pv-b1-probe"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath="lib.rs"\n[dependencies]\naspis-core={path="'+str(H/'candidate/src/crates/aspis-core')+'",features=["r0","ct-host-prover"]}\n[profile.release]\nopt-level=3\noverflow-checks=false\n')
llbc=H/f'PV_B1_{op}.llbc'
cmd=['timeout','180','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract','CARGO_TARGET_DIR='+str(H/'charon-target'),str(X/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::'+name,'--include','pv_b1_probe::*','--include','aspis_core::field::*','--dest-file',str(llbc),'--','--manifest-path',str(p/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
run(f'charon-{op}-{suffix}',cmd,p)
o=H/f'generated-{op}';o.mkdir(exist_ok=True)
run(f'aeneas-{op}-{suffix}',['timeout','180',str(PIN),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_B1_{op}','-dest',str(o),'-split-files','-emit-json',str(llbc)],p)
