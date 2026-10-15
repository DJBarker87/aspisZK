#!/usr/bin/env python3
"""Run pinned Charon/Aeneas extraction for the isolated unrolled candidate."""
from __future__ import annotations
import argparse, hashlib, json, os, shutil, subprocess
from pathlib import Path
CHARON=Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon')
AENEAS=Path('/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/aeneas-repro-r1')
TOOLS={CHARON:'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c',AENEAS:'e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v): p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--input',type=Path,required=True); ap.add_argument('--output',type=Path,required=True); ap.add_argument('--entry',default='crate::parse_wide_exact_probe'); ap.add_argument('--namespace',default='AspisR1UnrolledWideParser'); ap.add_argument('--monomorphize',action='store_true'); ap.add_argument('--mir',choices=['built','promoted','elaborated','optimized'],default='built'); a=ap.parse_args()
 for p,h in TOOLS.items(): assert sha(p)==h,p
 pins=json.loads((a.input/'source-pins.json').read_text())
 for rel,r in pins['sources'].items(): assert sha(a.input/rel)==r['sha256'],rel
 assert not a.output.exists(); a.output.mkdir(parents=True)
 shutil.copy2(Path(__file__),a.output/'extract-runner.py'); src=a.output/'source'; src.mkdir()
 for rel in ['Cargo.toml','lib.rs','source-pins.json',*pins['sources']]:
  dst=src/rel; dst.parent.mkdir(parents=True,exist_ok=True); shutil.copy2(a.input/rel,dst)
 env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=str(a.output/'target'),NO_DNA='1')
 write(a.output/'environment.json',{k:env[k] for k in ['PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','CARGO_TARGET_DIR','NO_DNA']})
 write(a.output/'tool-pins.json',{str(p):h for p,h in TOOLS.items()}); write(a.output/'input-pins.json',{str(p.relative_to(src)):sha(p) for p in src.rglob('*') if p.is_file()})
 rec=[]
 def run(label,cmd):
  cmd=[str(x) for x in cmd]
  with (a.output/(label+'.log')).open('w') as log: r=subprocess.run(['/usr/bin/time','-v','-o',str(a.output/(label+'.time.log')),*cmd],cwd=src,env=env,stdout=log,stderr=subprocess.STDOUT)
  rec.append({'label':label,'command':cmd,'exit':r.returncode}); write(a.output/'commands.json',rec); print(json.dumps(rec[-1]),flush=True)
  if r.returncode: print((a.output/(label+'.log')).read_text()[-8000:],flush=True); raise SystemExit(r.returncode)
 run('rustc-version',['rustc','--version','--verbose']); run('lock',['cargo','generate-lockfile','--offline'])
 run('extract',[CHARON,'cargo','--preset','aeneas','--mir',a.mir,'--sysroot','default',*(['--monomorphize'] if a.monomorphize else []),'--include','core::option','--include','core::result','--start-from',a.entry,'--dest-file',a.output/'R1FieldParser.llbc','--','--locked','--offline','--release','--lib','--no-default-features'])
 run('translate',[AENEAS,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',a.namespace,'-dest',a.output/'generated','-subdir',a.namespace,'-split-files','-emit-json',a.output/'R1FieldParser.llbc'])
 arts={str(p.relative_to(a.output)):sha(p) for d in [src,a.output/'generated'] for p in d.rglob('*') if p.is_file()}; arts['R1FieldParser.llbc']=sha(a.output/'R1FieldParser.llbc'); write(a.output/'artifact-pins.json',arts)
 print(json.dumps({'status':'TRANSLATED','pinned_artifacts':len(arts),'scope':'Generated source only; not yet Lean-checked or refined.'}),flush=True)
if __name__=='__main__': main()
