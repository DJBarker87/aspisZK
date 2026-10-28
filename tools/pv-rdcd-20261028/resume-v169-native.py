from pathlib import Path
import os,subprocess,json,hashlib,sys
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');P=D/'classification-project-fixture';O=D/'resume-v169-original-route'
base=(D/'classify-project-focused-leaves/fixture.rs.txt').read_bytes()
extra=b'''\n#[test] fn take_layouts() {
 use std::mem::{size_of,align_of};
 assert_eq!((size_of::<M31>(),align_of::<M31>()),(4,4));
 assert_eq!((size_of::<QM31>(),align_of::<QM31>()),(16,4));
 let m=Vec::<M31>::default();let q=Vec::<QM31>::default();
 assert_eq!((m.as_ptr() as usize,m.len(),m.capacity()),(4,0,0));
 assert_eq!((q.as_ptr() as usize,q.len(),q.capacity()),(4,0,0));
 println!("V169 deployed constant layouts:M31(4,4),QM31(16,4); empty default metadata(address,len,cap)=(4,0,0); finite typed metadata validation");
}\n'''
(P/'fixture.rs').write_bytes(base+extra)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'classification-target'),CARGO_BUILD_JOBS='4')
cmd=['cargo','test','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--locked','-j','4','--lib','take','--','--nocapture','--test-threads=1']
m=json.loads(subprocess.check_output(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--offline','--locked','--format-version','1'],env=env,text=True));nodes={x['id']:x for x in m['resolve']['nodes']}
(O/'native-inputs.json').write_text(json.dumps(dict(command=cmd,toolchain=subprocess.check_output(['rustc','-vV'],env=env,text=True),features=[dict(name=p['name'],version=p['version'],features=nodes[p['id']]['features']) for p in m['packages']],profile='release opt3 debug_assertions=false overflow_checks=false',original_fixture_sha256=hashlib.sha256(base).hexdigest(),compiled_fixture_sha256=hashlib.sha256(base+extra).hexdigest(),extra_test=extra.decode(),reason='new source/default laws and complete concrete constructor binding; no field source changed; finite validation only'),indent=2)+'\n')
print('Expected time: optimized cached compilation then130 take fixtures and two type/layout metadata cases',flush=True)
sys.exit(subprocess.run(cmd,env=env).returncode)
