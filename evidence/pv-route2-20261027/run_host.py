from pathlib import Path
import subprocess,json,time,hashlib,sys,os
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027'); G=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'); BASE=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027')
REV=(D/'revision').read_text().strip()
def run(name,cmd,cwd=None):
 O=D/name;O.mkdir();(O/'target.json').write_text(json.dumps(dict(target=cmd,cwd=str(cwd),revision=REV,preflight=True,print_axioms='N/A extraction'),indent=2));a=subprocess.run(['python3',str(G/'reservation.py'),str(O/'admission-before.json')],stdout=open(O/'reservation.log','w'),stderr=subprocess.STDOUT)
 if a.returncode:return a.returncode
 start=time.monotonic();r=subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G/'barrier.py'),str(O/'admission-barrier.json'),'/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=cwd,stdout=open(O/'output.log','w'),stderr=subprocess.STDOUT)
 (O/'receipt.json').write_text(json.dumps(dict(exit=r.returncode,wall_seconds=time.monotonic()-start,revision=REV,print_axioms='N/A extraction',time_log=(O/'time.log').read_text() if (O/'time.log').exists() else None),indent=2)); print(name,r.returncode,flush=True);return r.returncode
roots={79:'eval_message',223:'compress_tagged_tuple',230:'state_only_copy_helper_sum',249:'gamma_sample',250:'ordinary_sample',254:'powers',258:'all_slots_clear'}
for op in map(int,sys.argv[1:]):
 P=D/'probes'/str(op);P.mkdir(parents=True,exist_ok=True);(P/'Cargo.toml').write_text('[package]\nname="pv-r2-probe"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath="lib.rs"\n[dependencies]\naspis-core={path="'+str(BASE/'source/crates/aspis-core')+'",features=["r0","ct-host-prover"]}\n[profile.release]\nopt-level=3\noverflow-checks=false\n');(P/'lib.rs').write_bytes((D/'probe-inputs'/f'{op}.rs').read_bytes())
 llbc=D/f'PV_R2_{op}.llbc';cmd=['timeout','180','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract','CARGO_TARGET_DIR='+str(D/'charon-target'),str(BASE/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::'+roots[op],'--include','pv_r2_probe::*','--include','aspis_core::field::*','--dest-file',str(llbc),'--','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
 if run(f'charon-{op}-01',cmd,P):continue
 out=D/f'generated-{op}';out.mkdir();run(f'aeneas-{op}-01',['timeout','180','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_R2_{op}','-dest',str(out),'-split-files','-emit-json',str(llbc)])
