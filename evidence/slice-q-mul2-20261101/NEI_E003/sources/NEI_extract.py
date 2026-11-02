from pathlib import Path
import subprocess,json,hashlib,os
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon')
A=C.with_name('aeneas-b59d5188-extended')
# Restore frozen reached crate bytes in a private scratch scaffold.
import shutil
frozen=json.loads((B/'NEI_FROZEN.json').read_text())
scratch=B/'NEI_src'
if not scratch.exists():
 old=B.parent/'codex-cx-native-cpilot-20261028/NCO_src'
 scratch.mkdir()
 for p in old.rglob('*'):
  if not p.is_file():continue
  n=str(p.relative_to(old))
  if any(v.startswith(('NCO_','NCH_')) for v in Path(n).parts):continue
  if n in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']:continue
  q=scratch/n;q.parent.mkdir(parents=True,exist_ok=True)
  if n in frozen:q.write_text(frozen[n])
  elif p.name=='Cargo.toml':q.write_bytes(p.read_bytes())
  else:q.symlink_to(p.resolve())
# Never restore over a drifted frozen lock. A mismatch is a finding, not repair.
if (scratch/'Cargo.lock').exists():
 assert (scratch/'Cargo.lock').read_text()==frozen['Cargo.lock'],'STOP existing frozen lock drift before extraction'
for n,t in frozen.items():
 if n.startswith(('crates/','programs/')) and not (scratch/Path(n).parts[0]/Path(n).parts[1]).exists():continue
 q=scratch/n;q.parent.mkdir(parents=True,exist_ok=True)
 if q.is_symlink():q.unlink()
 if not q.exists() or q.read_text()!=t:q.write_text(t)
cfg=json.loads(os.environ['NEI_EXTRACT_CONFIG']); ns=cfg['namespace'];out=B/'NEI_extracted'/ns;out.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=B/'NEI_src/crates/aspis-r1-cost-probe/Cargo.toml'
if cfg.get('isolate'):
 import re
 src=(B/'NEI_src/crates/aspis-r1-cost-probe/src/verifier.rs').read_text()
 def take(name):
  m=re.search(r'\bfn '+name+r'\b',src);start=src.index('{',m.start());i=start+1;d=1
  while d:
   if src[i]=='{':d+=1
   elif src[i]=='}':d-=1
   i+=1
  return src[m.start():i]
 mini=B/'NEI_isolated';(mini/'src').mkdir(parents=True,exist_ok=True)
 (mini/'Cargo.toml').write_text('[package]\nname="neg_isolated"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[features]\nprivate-leaf-salts=[]\noptimized-terminal=[]\nprogram-build=[]\n[dependencies]\naspis-core={path="../NEI_src/crates/aspis-core",features=["r0"]}\n')
 prelude='extern crate alloc;\nuse alloc::vec::Vec;\nuse aspis_core::field::{M31,QM31 as K,WideExact as E};\nconst QUARTER:M31=M31(536870912);\n'
 funcs=['residue_limb_at','power_limb_at','update_residue_row','batch_prefix_products','circle_fold_with_inverses','line_fold_with_inverses']
 prelude+='\n'.join(take(n) for n in funcs)
 prelude+='\nstruct BatchedWeights { raw:Vec<[u64;4]>, terms:usize }\nimpl BatchedWeights{'+take('push')+'}\n'
 prelude+='\n#[path="../../NEI_src/crates/aspis-r1-cost-probe/src/fast_pairing.rs"] mod fast_pairing;\n#[path="../../NEI_src/crates/aspis-r1-cost-probe/src/fast_dots.rs"] mod fast_dots;\n'
 (mini/'src/lib.rs').write_text(prelude)
 manifest=mini/'Cargo.toml'
 if cfg.get('row_reference'):(mini/'src/lib.rs').write_bytes((B/'NEI_row_reference.rs').read_bytes())
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NEI_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
cmd=[str(C),'cargo','--preset','aeneas','--mir',cfg.get('mir','built'),'--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
for root in cfg['roots']:cmd+=['--start-from',root]
cmd+=cfg.get('charon_options',[])
llbc=B/(ns+'.llbc')
cmd+=['--dest-file',str(llbc),'--','--manifest-path',str(manifest),'--offline','--release','--lib','--jobs','1','--features','private-leaf-salts,optimized-terminal,program-build']
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,toolchain='nightly-2026-09-17',lock_before=sha(B/'NEI_src/Cargo.lock'),actual_source={p:sha(B/'NEI_src'/p) for p in ['crates/aspis-r1-cost-probe/src/fast_dots.rs','crates/aspis-r1-cost-probe/src/verifier.rs']})
(B/'NEI_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2));print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=manifest.parent,env=env)
pins['charon_exit']=r.returncode
if not r.returncode:
 pins['llbc_sha256']=sha(llbc)
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest',str(B/'NEI_extracted'),'-subdir',ns,'-split-files']+cfg.get('aeneas_options',[])+[str(llbc)]
 pins['aeneas_command']=cmd;print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=B,env=env)
pins.update(exit=r.returncode,lock_after=sha(B/'NEI_src/Cargo.lock'),outputs={str(p.relative_to(B)):sha(p) for p in out.rglob('*') if p.is_file()})
(B/'NEI_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
assert pins['lock_before']==pins['lock_after'],'LOCK DRIFT STOP'
raise SystemExit(r.returncode)
