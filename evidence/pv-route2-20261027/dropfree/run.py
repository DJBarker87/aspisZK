from pathlib import Path
import sys,os,json,hashlib,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027/dropfree');BASE=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027')
s=(D.parent/'run_host.py').read_text().split('roots=')[0];s=s.replace("D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027')","D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027/dropfree')");exec(s)
raw_run=run
def run(name,cmd,cwd=None):
 for admission in range(11):
  tag=name if admission==0 else name+f'-admission{admission}'
  try: result=raw_run(tag,cmd,cwd)
  except SystemExit as e: result=int(e.code)
  O=D/tag
  if (O/'time.log').exists(): return result
  log=''.join(p.read_text() for p in O.glob('*reservation*.log'))
  if 'FileNotFoundError' in log:
   if admission: raise SystemExit('Repeated transient scanner failure; lead repair required: '+log)
   wait=30
  elif 'allowed' in log and ('false' in log or 'QUIET' in log): wait=180
  else: raise SystemExit('Admission failure: '+log)
  print(tag,'admission only; waiting',wait,'seconds',flush=True)
  if admission==10:raise SystemExit(result)
  time.sleep(wait)
 return result
roots={249:'gamma_sample',250:'ordinary_sample',252:'weights_new',226:'public_bytes',134:'active_row_masks',36:'array_try_from',205:'finalize_variable_core',212:'finalize',215:'finalize_into',216:'update',217:'new',219:'finalize_fixed_core'}
for op in map(int,sys.argv[1:]):
 suffix=os.environ.get('VARIANT','01');name=f'{op}-{suffix}';P=D/'packages'/name;P.mkdir(parents=True,exist_ok=True)
 (P/'Cargo.toml').write_text('[package]\nname="pv-r2-dropfree"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath="lib.rs"\n[dependencies]\naspis-core={path="'+str(BASE/'source/crates/aspis-core')+'",features=["r0","ct-host-prover"]}\n[profile.release]\nopt-level=3\noverflow-checks=false\n')
 (P/'lib.rs').write_bytes((D/'probes'/f'{op}.rs').read_bytes());llbc=D/f'PV_R2_DF_{op}_{suffix}.llbc'
 cmd=['timeout','180','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract','CARGO_TARGET_DIR='+str(D.parent/'charon-target'),str(BASE/'charon'),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::'+roots[op],'--include','pv_r2_dropfree::*','--include','aspis_core::field::*','--dest-file',str(llbc),'--','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
 if run('charon-'+name,cmd,P):continue
 out=D/('generated-'+name);out.mkdir();run('aeneas-'+name,['timeout','180','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_R2_DF_{op}_{suffix}','-dest',str(out),'-split-files','-emit-json',str(llbc)])
