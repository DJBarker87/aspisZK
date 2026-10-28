"""Pinned extractor; private driver, deployed feature/dependency selection (x')."""
from pathlib import Path
import os,subprocess,json,hashlib,sys
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028'); O=D/'resume-v212';O.mkdir(exist_ok=True)
T=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools')
pins={'aeneas':'562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19','charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','charon-driver':'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45'}
for n,h in pins.items():assert hashlib.sha256((T/n).read_bytes()).hexdigest()==h,n
P=D/'classification-project-fixture'
manifest=(P/'Cargo.toml').read_text().replace('path="fixture.rs"','path="lib.rs"')
(O/'Cargo.toml').write_text(manifest);(O/'Cargo.lock').write_bytes((P/'Cargo.lock').read_bytes())
(O/'lib.rs').write_text('pub fn qm_inv(x: aspis_core::field::QM31) -> Option<aspis_core::field::QM31> { <aspis_core::field::QM31 as aspis_core::r0::scalar::CodeField>::try_inv(x) }\n')
env=dict(os.environ,PATH=str(T)+':/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_TARGET_DIR=str(D/'resume-extract-target'),CARGO_BUILD_JOBS='4')
meta=subprocess.run(['cargo','metadata','--manifest-path',str(O/'Cargo.toml'),'--offline','--locked','--format-version','1'],env=env,capture_output=True,text=True);assert meta.returncode==0,meta.stderr
m=json.loads(meta.stdout);nodes={n['id']:n for n in m['resolve']['nodes']}
features=[dict(name=p['name'],version=p['version'],features=nodes[p['id']]['features']) for p in m['packages']]
cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::qm_inv','--include','aspis_core::field','--include','aspis_core::r0::scalar','--include','core::option','--dest-file',str(O/'PV_RDCD_V212.llbc'),'--','--manifest-path',str(O/'Cargo.toml'),'--release','--offline','--locked','--lib','--jobs','4']
record=dict(command=cmd,tool_pins=pins,tool_pin_authority='committed evidence/pv-cb9-20261027/cb9-op254-charon/receipt.json; driver retained companion',features=features,profile=dict(name='release',debug_assertions=False,overflow_checks=False,opt_level=3),toolchain=subprocess.check_output(['rustc','-vV'],env=env,text=True),inputs={n:hashlib.sha256((O/n).read_bytes()).hexdigest() for n in ['Cargo.toml','Cargo.lock','lib.rs']},qualification='x prime: extraction toolchain only; native remains1.94.1; no cfg kani or pv_cb_extract injected')
(O/'inputs.json').write_text(json.dumps(record,indent=2)+'\n')
print('Expected time: optimized compilation then named V212 shipped-root extraction',flush=True)
sys.exit(subprocess.run(cmd,env=env).returncode)
