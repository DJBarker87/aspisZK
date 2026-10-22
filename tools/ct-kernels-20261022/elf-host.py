#!/usr/bin/env python3
from pathlib import Path
import os,subprocess,hashlib,json,sys
R=Path(__file__).resolve().parents[2]; H=R.parent
stage=sys.argv[1] if len(sys.argv)>1 else 's3a'
assert stage.replace('-','').isalnum()
F=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020/artifacts')
rows=[]
subprocess.run(['python3',str(R/'tools/ct-kernels-20261022/refresh-project-mtimes.py'),str(R)],check=True)
for mode,pin,manifest,features,filename in [
 ('default','40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0','r1-cost-probe','pool-adapter,private-leaf-salts','aspis_r1_cost_probe_program.so'),
 ('devnet','12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f','r1-cost-probe','pool-adapter,private-leaf-salts','aspis_r1_cost_probe_program.so'),
 ('pool','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548','aspis-pool','r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit','aspis_pool.so')]:
 env=dict(os.environ,CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4',CT_EXPECTED='Optimized SBF compilation/link and frozen ELF identity; no proof generation')
 for k in ['ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID','CARGO_ENCODED_RUSTFLAGS']:env.pop(k,None)
 if mode=='devnet':env.update(ASPIS_R1_POOL_PROGRAM_ID='BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs',ASPIS_R1_REGISTRY_PROGRAM_ID='9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q')
 env['RUSTC_WRAPPER']=str(R/'tools/ct-kernels-20261022/rustc-bounded.sh')
 out=H/'artifacts'/(stage+'-'+mode);out.mkdir(parents=True,exist_ok=False)
 cmd=['env','-u','RUSTFLAGS','/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(R/'programs'/manifest/'Cargo.toml'),'--sbf-out-dir',str(out),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
 code=subprocess.run(['python3',str(R/'tools/ct-kernels-20261022/run-host.py'),'elf-'+stage+'-'+mode,*cmd],env=env).returncode
 for key in out.glob("*keypair.json"):key.chmod(0o600)
 artifact=out/filename
 row=dict(mode=mode,exit_status=code,expected_sha256=pin)
 if artifact.exists():
  row.update(sha256=hashlib.sha256(artifact.read_bytes()).hexdigest(),bytes=artifact.stat().st_size,byte_equal=hashlib.sha256(artifact.read_bytes()).hexdigest()==pin)
 rows.append(row);(R/'elf-identities.json').write_text(json.dumps(rows,indent=2)+'\n')
 if code or not row.get('byte_equal'):raise SystemExit(1)
