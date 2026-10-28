from pathlib import Path
import subprocess,os,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028');F=D.parent/'codex-pv-fscan-20261028';S=F/'src'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',RUSTC_BOOTSTRAP='1',CARGO_TARGET_DIR=str(D/'unit-target'))
cmd=['cargo','build','--release','--locked','--manifest-path',str(S/'tools/r1-cost-probe/Cargo.toml'),'-p','aspis-r1-cu-probe','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','devnet_spend','-j','4','-Z','unstable-options','--unit-graph']
r=subprocess.run(cmd,env=env,capture_output=True,text=True);(D/'unit-graph.stderr').write_text(r.stderr);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);(D/'unit-graph.json').write_text(r.stdout)
features=[dict(package_id=x['pkg_id'],features=x['features'],profile=x['profile'],target=x['target']) for x in j['units']];(D/'resolved-features.json').write_text(json.dumps(features,indent=2))
old=json.loads((F/'units-client-bin/unit-graph.json').read_text());assert j==old,'deployed feature graph changed'
print('Exact client unit graph reproduced:',len(features),'units; rustc 1.94.1; release; explicit client features')
