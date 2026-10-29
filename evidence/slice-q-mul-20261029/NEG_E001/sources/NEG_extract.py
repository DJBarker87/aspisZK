from pathlib import Path
import subprocess,json,hashlib,os
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon')
A=C.with_name('aeneas-b59d5188-extended')
cfg=json.loads(os.environ['NEG_EXTRACT_CONFIG']); ns=cfg['namespace'];out=B/'NEG_extracted'/ns;out.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=B/'NEG_src/crates/aspis-r1-cost-probe/Cargo.toml'
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NEG_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
cmd=[str(C),'cargo','--preset','aeneas','--mir',cfg.get('mir','built'),'--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
for root in cfg['roots']:cmd+=['--start-from',root]
cmd+=cfg.get('charon_options',[])
llbc=B/(ns+'.llbc')
cmd+=['--dest-file',str(llbc),'--','--manifest-path',str(manifest),'--offline','--release','--lib','--jobs','1','--features','private-leaf-salts,optimized-terminal,program-build']
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,toolchain='nightly-2026-09-17',lock_before=sha(B/'NEG_src/Cargo.lock'),actual_source={p:sha(B/'NEG_src'/p) for p in ['crates/aspis-r1-cost-probe/src/fast_dots.rs','crates/aspis-r1-cost-probe/src/verifier.rs']})
(B/'NEG_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2));print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=manifest.parent,env=env)
pins['charon_exit']=r.returncode
if not r.returncode:
 pins['llbc_sha256']=sha(llbc)
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest',str(B/'NEG_extracted'),'-subdir',ns,'-split-files']+cfg.get('aeneas_options',[])+[str(llbc)]
 pins['aeneas_command']=cmd;print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=B,env=env)
pins.update(exit=r.returncode,lock_after=sha(B/'NEG_src/Cargo.lock'),outputs={str(p.relative_to(B)):sha(p) for p in out.rglob('*') if p.is_file()})
(B/'NEG_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
assert pins['lock_before']==pins['lock_after'],'LOCK DRIFT STOP'
raise SystemExit(r.returncode)
