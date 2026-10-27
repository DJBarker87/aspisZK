"""Build a single identical harness on base/candidate; restore all swapped inputs."""
from run import H,run
from pathlib import Path
import subprocess,hashlib,json,sys
which,suffix=sys.argv[1:];assert which in ['base','candidate']
S=H/'source';D=S/'evidence/pv-batch3-20261027';base=H/'fixture-base-input'
files=json.loads((D/'fixture-base-files.json').read_text()) if which=='base' else []
backups={p:(S/p).read_bytes() for p in files}
manifest=S/'crates/aspis-r1-cost-probe/Cargo.toml';mb=manifest.read_bytes()
example=S/'crates/aspis-r1-cost-probe/examples/pv_b3_bytes.rs';assert not example.exists()
try:
 for p in files:(S/p).write_bytes((base/p).read_bytes())
 example.write_bytes((D/'fixture_bytes.rs').read_bytes())
 manifest.write_text(manifest.read_text()+'\n[[example]]\nname="pv_b3_bytes"\nrequired-features=["r1p-check","ct-host-prover"]\n')
 cmd=['timeout','300','taskset','--cpu-list','0-3','cargo','build','--release','--locked','--offline','-j','4','-p','aspis-r1-cost-probe','--features','optimized-terminal,r1p-check,ct-host-prover','--example','pv_b3_bytes']
 status=run('fixture-bytes-build-'+which+'-'+suffix,cmd,'optimized compilation only; exact base37/candidate fixture-byte harness',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'})
 if status==0:
  binary=H/'target/release/examples/pv_b3_bytes';dest=H/('bin/pv_b3_bytes_'+which);dest.write_bytes(binary.read_bytes());dest.chmod(0o755)
  (H/('fixture-bytes-binary-'+which+'.json')).write_text(json.dumps(dict(binary_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(example.read_bytes()).hexdigest(),source_revision='37e5e133f89f4aa5909a1ca6fc81237d2c977947' if which=='base' else (H/'revision').read_text().strip(),files={p:hashlib.sha256((S/p).read_bytes()).hexdigest() for p in files}),indent=2)+'\n')
finally:
 for p,b in backups.items():(S/p).write_bytes(b)
 manifest.write_bytes(mb);example.unlink()
sys.exit(status)
