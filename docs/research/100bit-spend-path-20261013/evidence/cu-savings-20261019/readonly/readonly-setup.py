from pathlib import Path
import json,shutil,hashlib
w=Path('/home/dombarker/project-offloads/aspis-r1-cu-savings-20261019');d=Path('/home/dombarker/project-offloads/aspis-r1-decision1h-20261019')
shutil.copytree(d/'source',w/'readonly');shutil.copy2(w/'readonly_runtime.rs',w/'readonly/tools/r1-cost-probe/src/bin/r18_replay/readonly_runtime.rs')
build={'command':['/home/dombarker/.cargo/bin/cargo','build','--verbose','--release','--locked','--offline','-j1','--manifest-path','tools/r1-cost-probe/Cargo.toml','--features','private-leaf-salts,litesvm/persistence-internal','--bin','r18_replay'],'cwd':str(w/'readonly'),'out':str(w/'runs/readonly-driver-build'),'source_revision':'67163f90b (1h baseline source + driver-only repair; exact file manifest retained)','features':['private-leaf-salts','litesvm/persistence-internal'],'env':{'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN':'stable','CARGO_TARGET_DIR':str(d/'native-target'),'CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true'},'expected_time':'optimized native driver compilation; no proof generation or SBF build'}
(w/'readonly-build.json').write_text(json.dumps(build,indent=2))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();manifest={str(p.relative_to(w/'readonly')):sha(p) for p in (w/'readonly').rglob('*') if p.is_file()};(w/'readonly-inputs.json').write_text(json.dumps(manifest,indent=2))
