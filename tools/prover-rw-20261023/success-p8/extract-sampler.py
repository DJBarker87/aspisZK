"""Owned indexed ordinary reference; use unmodified pinned extractor."""
from pathlib import Path
import os,subprocess
r=Path(__file__).resolve().parents[3]
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','aspis_core','--opaque','aspis_statement','--start-from','crate::sampler_owned::ordinary_sample']
for x in ['crate::sampler_owned','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact','aspis_core::field::P']:
 cmd+=['--include',x]
cmd+=['--dest-file',str(r/'PV_OrdinaryOwned.llbc'),'--','--manifest-path',str(Path(__file__).with_name('proof')/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
