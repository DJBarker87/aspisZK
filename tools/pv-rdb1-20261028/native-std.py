"""Replay historical finite fixtures with the deployed stable compiler/profile."""
from pathlib import Path
import os,sys,subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028')
F=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028')
suite=sys.argv[1]; out=D/('native-'+suite);out.mkdir(exist_ok=True)
files={'std-extra':'classify-std-fixture.rs','drop':'drop-u32.rs','join':'v178.rs','append':'v182.rs','reserve':'reserve-native.rs','pop':'pop-move-world.rs','pop-zst':'pop-zst-world.rs','array':'array-owned-reference.rs'}
p=F/'classification-inputs'/files[suite]
rustc='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc'
env=dict(os.environ,RUSTUP_TOOLCHAIN='1.94.1')
if suite=='reserve':env['RUSTC_BOOTSTRAP']='1'
cmd=[rustc,'--edition=2021','-Copt-level=3','-Cdebug-assertions=false','-Coverflow-checks=false','-Cpanic=unwind',str(p),'-o',str(out/'check')]
if suite=='array':cmd+=['--test']
features=json.loads((F/'units-client-bin/features.json').read_text())
(out/'configuration.json').write_text(json.dumps(dict(toolchain=subprocess.check_output([rustc,'-vV'],text=True),profile={'name':'release','opt_level':3,'debug_assertions':False,'overflow_checks':False,'panic':'unwind'},resolved_client_crates=features,fixture_crates='std/alloc/core only; no project feature-bearing crate is linked by these std-only fixtures',source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),command=cmd,bootstrap='try_reserve_kind inspection only' if suite=='reserve' else False,evidence_class='finite native differential; not universal proof'),indent=2))
subprocess.run(cmd,env=env,check=True)
subprocess.run([str(out/'check')]+(['--nocapture','--test-threads=1'] if suite=='array' else []),check=True,env=env)
