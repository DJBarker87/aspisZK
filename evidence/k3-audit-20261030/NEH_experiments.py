"""K-3 diagnostics; deliberate writable statics earn no verification credit."""
from NEH_host import *
import os
TYPE=os.environ.get('NEH_TYPE','usize');INIT=os.environ.get('NEH_INIT','0');WRITE=os.environ.get('NEH_WRITE','1');LITERAL=os.environ.get('NEH_LITERAL','0');PRED=os.environ.get('NEH_PRED','obs==1')
MODE=os.environ.get('NEH_MODE','mut')
a=sys.argv[1] if False else __import__('sys').argv[1]
static={'mut':f'static mut NBZ_Q:usize={INIT};','cell':f'static NBZ_Q:core::sync::atomic::AtomicUsize=core::sync::atomic::AtomicUsize::new({INIT});','unwritten':f'static NBZ_Q:usize={INIT};','local':f''}[MODE]
write={'mut':f'unsafe{{NBZ_Q={WRITE};}}','cell':f'NBZ_Q.store({WRITE},core::sync::atomic::Ordering::SeqCst);','unwritten':'let _read=NBZ_Q;','local':f'let mut record={INIT}usize; record={WRITE}; assert!(record=={WRITE});'}[MODE]
s=f'''use super::*;
{static}
fn NBZ_mark_none(obs:{TYPE},phase:Phase) {{
 assert!({PRED});
 let _=phase;
}}
#[kani::proof]
#[kani::unwind(8)]
fn NBZ_return_carriers() {{
 {write}
 NBZ_mark_none({LITERAL},Phase::Query(1));
}}
'''
if os.environ.get('NEH_SOURCE_FILE'):s=Path(os.environ['NEH_SOURCE_FILE']).read_text()
(E/(a+'.rs')).write_text(s)
files={'NEH_src/crates/aspis-r1-cost-probe/src/NBZ_native.rs':s}
for n in ['NEH_gate.py','NEH_graph.py']:files[n]=(E/n).read_text()
admit(a+'_INPUT')
r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r});(b/'NEH_tmp').mkdir(exist_ok=True)
for n,t in {files!r}.items():(b/n).write_text(t)
p=b/'NEH_src';candidate=p/'crates/aspis-r1-cost-probe/src/candidate.rs'
if 'mod NBZ_native;' not in candidate.read_text():candidate.write_text(candidate.read_text()+chr(10)+'#[cfg(kani)] mod NBZ_native;'+chr(10))
pins={{str(q.relative_to(p)):hashlib.sha256(q.read_bytes()).hexdigest() for q in p.rglob('*') if q.is_file() and q.suffix in ['.rs','.toml','.lock']}}
(b/'NEH_SOURCE_PINS.json').write_text(json.dumps(pins))
print(len(pins))
''');assert r.returncode==0,r.stderr
ni=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NEH_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NEH_target','--lib','--features','private-leaf-salts,optimized-terminal,program-build','-j','1','-Z','unstable-options','-Z','stubbing','--harness-timeout','30s','--exact','--harness','verifier::candidate::NBZ_native::NBZ_return_carriers','--output-format','regular']
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NEH_tmp')
cfg=dict(attempt=a,kind='kani',module=ni[-3],sources=list(files)+['NEH_src/Cargo.lock'],command=['python3','NEH_gate.py',a+'.json'],native_command=ni,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},copy_patch_sha256=None,expected_time='Optimized compilation and tiny K-3 alias diagnostic; no multiplication or copied buffer',diagnostic=dict(type=TYPE,initializer=INIT,write=WRITE,literal=LITERAL,predicate=PRED,mode=MODE),print_axioms='N/A: kani')
launch(cfg)
r=py(f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{p.name:p.read_text() for p in b.glob({(a+'-*check.json')!r})}}))
''');assert r.returncode==0
for n,t in json.loads(r.stdout).items():(E/n).write_text(t)
