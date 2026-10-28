from pathlib import Path
import json,os,subprocess,sys,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');P=D/'classification-project-fixture';O=D/'resume-v212';
# Restore this job's exact previously recorded fixture, not another source snapshot.
s=(D/'classify-project-focused-leaves/fixture.rs.txt').read_bytes();(P/'fixture.rs').write_bytes(s)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'classification-target'),CARGO_BUILD_JOBS='4')
cmd=['cargo','test','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','--offline','-j','4','--lib','inverses','--','--nocapture','--test-threads=1']
metadata=json.loads(subprocess.check_output(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--offline','--locked','--format-version','1'],env=env,text=True));nodes={n['id']:n for n in metadata['resolve']['nodes']}
(O/'native-inputs.json').write_text(json.dumps(dict(command=cmd,toolchain=subprocess.check_output(['rustc','-vV'],env=env,text=True),fixture_sha256=hashlib.sha256(s).hexdigest(),features=[dict(name=p['name'],version=p['version'],features=nodes[p['id']]['features']) for p in metadata['packages']],profile='release opt3 debug_assertions=false overflow_checks=false',reason='new deployed extraction and completed source-law obligations; focused final native gate, finite validation only'),indent=2)+'\n')
print('Expected time: optimized compilation then3075 inverse pairs per type; no elimination',flush=True)
sys.exit(subprocess.run(cmd,env=env).returncode)
