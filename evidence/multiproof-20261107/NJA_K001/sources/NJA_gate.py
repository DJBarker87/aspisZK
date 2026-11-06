"""Owned frozen graph and scratch source validation before EVERY Kani run."""
from pathlib import Path
import sys,json,hashlib,subprocess,os,base64,lzma,difflib
import NJA_stage as stage
E=Path(__file__).resolve().parent;x=json.loads((E/sys.argv[1]).read_text());a=x['attempt'];S=E/'NJA_workspace';out=E/(a+'_validation');out.mkdir(exist_ok=False)
# Only restore our prior scratch harness before re-validating every frozen byte.
p=S/'crates/aspis-r1-cost-probe/src/multiproof.rs';payload=json.loads(lzma.decompress((E/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes()));raw=base64.b64decode(payload[str(p.relative_to(S))]);h=(E/'NJA_harness.rs').read_bytes()
if p.exists():assert p.read_bytes() in (raw,raw+b'\n'+h), 'unexpected scratch drift'
p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
manifest=stage.validate(S,out,'/home/dombarker/.cargo/bin/cargo');frozen=manifest['files']['Cargo.lock']['sha256'];p.write_bytes(raw+b'\n'+h)
assert not any(t in h.decode() for t in ['static mut','UnsafeCell','Atomic','Cell<','RefCell'])
patch=''.join(difflib.unified_diff(raw.decode().splitlines(True),p.read_text().splitlines(True),fromfile='a/'+str(p.relative_to(S)),tofile='b/'+str(p.relative_to(S))))
(out/'NJA_harness.patch').write_text(patch)
(out/'NJA_INPUTS.json').write_text(json.dumps(dict(frozen_revision=stage.REV,harness_sha256=stage.sha(h),patch_sha256=stage.sha(patch.encode()),cargo_target=os.environ['CARGO_TARGET_DIR'],copy_builtins_reached=False,source_sha256=stage.sha(raw),native_command=x['native_command']),indent=2)+'\n')
try:
 r=subprocess.run(x['native_command'],cwd=E)
finally:
 last=stage.sha((S/'Cargo.lock').read_bytes());(out/'NJA_LOCK.json').write_text(json.dumps(dict(before=frozen,after=last,unchanged=last==frozen))+'\n');assert last==frozen,'STOP lock drift';assert p.read_bytes()==raw+b'\n'+h
sys.exit(r.returncode)
