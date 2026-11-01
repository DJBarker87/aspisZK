"""Build audit copies with one additive input-capture call; never edit final sources."""
from pathlib import Path
import json,hashlib,subprocess,os,re
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');C=H/'src/tools/r1-cost-probe';O=H/'audit-src';assert O.is_dir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((H/'final-gates/audit-build.json').read_text());assert old['exit']==101
rows=old['source_copies']
for r in rows:
 assert sha(Path(r['source_root']))==r['source_root_sha256']
 assert sha(Path(r['source_plan']))==r['source_plan_sha256']
e=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/'native-target'),RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4')
c=['taskset','--cpu-list','0-3','cargo','+1.94.1','build','--manifest-path',str(O/'Cargo.toml'),'--profile','client','--locked','--offline','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bins']
r=subprocess.run(c,env=e)
x=dict(exit=r.returncode,command=c,source_copies=rows,export_source_sha256=sha(H/'audit_export.rs'),lock_byte_equal=(O/'Cargo.lock').read_bytes()==(C/'Cargo.lock').read_bytes(),binaries={p.name:sha(p) for p in (H/'native-target/client').glob('pv-uc-*-audit')})
(H/'final-gates/audit-build-fixed.json').write_text(json.dumps(x,indent=2)+'\n');raise SystemExit(r.returncode)
