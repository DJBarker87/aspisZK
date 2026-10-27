from pathlib import Path
import sys,runpy
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027/dropfree');args=sys.argv[:];sys.argv=[args[0]];globals().update(runpy.run_path(str(D/'run.py')));sys.argv=args
P=D/'native'
(P/'Cargo.toml').write_text('[package]\nname="pv-r2-dropfree-checks"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath="lib.rs"\n[dependencies]\naspis-core={path="'+str(BASE/'source/crates/aspis-core')+'",features=["r0","ct-host-prover"]}\n[profile.release]\nopt-level=3\noverflow-checks=false\n')
run('native-'+(args[1] if len(args)>1 else '01'),['timeout','180','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract','CARGO_TARGET_DIR='+str(D.parent/'charon-target'),'cargo','test','--release','--offline','--manifest-path',str(P/'Cargo.toml'),'--lib','--jobs','4'],P)
