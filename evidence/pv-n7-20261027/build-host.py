from pathlib import Path
import subprocess,sys,os,hashlib,json
H=Path('/home/dombarker/project-offloads/codex-pv-n7-20261027');which=sys.argv[1];R=H/which
# Expected time: optimized compilation and linking only, no proof generation.
cmd=['cargo','build','--manifest-path','tools/r1-cost-probe/Cargo.toml','--release','--offline','--locked','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','devnet_spend']
subprocess.run(cmd,cwd=R,check=True)
b=(H/'target/release/devnet_spend').read_bytes();(H/('devnet_spend-'+which)).write_bytes(b);(H/('devnet_spend-'+which)).chmod(0o700)
(H/'evidence'/('binary-'+which+'.json')).write_text(json.dumps(dict(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),command=cmd),indent=2)+'\n')
