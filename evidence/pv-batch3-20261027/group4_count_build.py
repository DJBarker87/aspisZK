"""Apply private instrumentation, build it, restore the exact candidate files."""
from run import H,run
from pathlib import Path
import subprocess,hashlib,json,sys
S=H/'source';D=S/'evidence/pv-batch3-20261027';p=S/'crates/aspis-prover/src/host_forest.rs';backup=p.read_bytes();mle=S/'crates/aspis-r1-cost-probe/src/host_multilinear.rs';mlebackup=mle.read_bytes();pubsource=S/'crates/aspis-r1-cost-probe/src/host_public.rs';pubbackup=pubsource.read_bytes();arithmetic=S/'crates/aspis-prover/src/host_arithmetic.rs';abackup=arithmetic.read_bytes();example=S/'crates/aspis-r1-cost-probe/examples/pv_b3_counts.rs';assert not example.exists()
manifest=S/'crates/aspis-r1-cost-probe/Cargo.toml';mbackup=manifest.read_bytes()
try:
 subprocess.run(['patch','-p1','--forward','--batch','-i',str(D/'group4-counts.patch')],cwd=S,check=True)
 example.write_text('#![cfg(feature="prover")]\n'+(D/'group4_fixture_counts.rs').read_text())
 manifest.write_text(manifest.read_text()+'\n[[example]]\nname="pv_b3_counts"\nrequired-features=["r1p-check","ct-host-prover"]\n')
 cmd=['timeout','300','taskset','--cpu-list','0-3','cargo','build','--release','--locked','--offline','-j','4','-p','aspis-r1-cost-probe','--features','optimized-terminal,r1p-check,ct-host-prover','--example','pv_b3_counts']
 result=run('fixture-count-build-'+sys.argv[1],cmd,'optimized compilation of fixture byte/count harness; no prover timing',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'})
 if result==0:
  binary=H/'target/release/examples/pv_b3_counts';dest=H/'bin/pv_b3_counts';dest.parent.mkdir(exist_ok=True);dest.write_bytes(binary.read_bytes());dest.chmod(0o755)
  rec=dict(binary_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),candidate_source_sha256=hashlib.sha256(backup).hexdigest(),instrumented_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scope='per-proof counts and byte commitments only; no whole-prover timing metric')
  (H/'fixture-count-binary.json').write_text(json.dumps(rec,indent=2)+'\n')
finally:
 p.write_bytes(backup);mle.write_bytes(mlebackup);pubsource.write_bytes(pubbackup);arithmetic.write_bytes(abackup);manifest.write_bytes(mbackup);example.unlink()
sys.exit(result)
