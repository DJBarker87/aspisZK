"""Expected time: cached optimized Rust compilation, then one singleton execution.
This checks GenericArray<u8,U64>::default only under own-2 triple-prime.
Core::default remains the original complete-Result parameter; it is not executed.
"""
from pathlib import Path
import json,subprocess,os,shutil,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028/rdcd4-20261029')
P=D/'singleton-project';O=D/'v237-singleton-artifacts';P.mkdir(exist_ok=True);O.mkdir(exist_ok=True)
original=D/'classify-project-encoder';manifest=(original/'Cargo.toml.txt').read_bytes();(P/'Cargo.toml').write_bytes(manifest)
lock=D/'classification-project-fixture/Cargo.lock';shutil.copy2(lock,P/'Cargo.lock')
source='''#[test]
fn singleton_default_bytes() {
    use generic_array::{GenericArray, typenum::U64};
    let bytes = GenericArray::<u8,U64>::default();
    let expected = [0u8;64];
    assert_eq!(bytes.as_slice(), &expected);
    let hex: String = bytes.iter().map(|x| format!("{x:02x}")).collect();
    println!("RDCD4_SINGLETON:{hex}");
}
''';(P/'fixture.rs').write_text(source)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'classification-target'),CARGO_BUILD_JOBS='2')
# The root source path differs, while every dependency version/feature remains
# identical. Keep the original V201 executable available at its recorded hash.
for p in (D/'classification-target/release/deps').glob('pv_fscan_deployed_project_fixture-*'):
 if p.is_file() and os.access(p,os.X_OK):
  dest=D/'retained-native-artifacts'/p.name;dest.parent.mkdir(exist_ok=True)
  if not dest.exists():shutil.copy2(p,dest)
meta=subprocess.run(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--offline','--locked','--format-version','1'],env=env,capture_output=True,text=True)
assert meta.returncode==0,meta.stderr;m=json.loads(meta.stdout);nodes={x['id']:x for x in m['resolve']['nodes']}
features=sorted((x['name'],x['version'],sorted(nodes[x['id']]['features'])) for x in m['packages'])
old=json.load(open(original/'inputs.json'))
for key in ['RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','RUSTC_BOOTSTRAP','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER']:
 assert env.get(key)==old['env'].get(key),('codegen environment changed',key)
expected=sorted((x['name'],x['version'],sorted(x['features'])) for x in old['features']);assert features==expected,(features,expected)
cmd=['cargo','test','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','-j','2','--lib','--','--nocapture','--test-threads=1']
pins=json.load(open(D/'buffer-dependency-sources.json'))
for x in pins:assert hashlib.sha256(Path(x['path']).read_bytes()).hexdigest()==x['sha256'],x['path']
record=dict(command=cmd,env={k:v for k,v in env.items() if k.startswith(('RUST','CARGO'))},profile='release opt3 overflow_checks=false debug_assertions=false panic=unwind',features=features,manifest_sha256=hashlib.sha256(manifest).hexdigest(),lockfile_sha256=hashlib.sha256(lock.read_bytes()).hexdigest(),fixture_source=source,fixture_sha256=hashlib.sha256(source.encode()).hexdigest(),classification='exhaustive over a singleton input domain, deployed-configuration harness',scope='GenericArray<u8,U64>::default exact64 bytes only; wrapper/Core Default are not claimed input-free.',rustc=subprocess.check_output(['rustc','-vV'],env=env,text=True),expected_phase='cached optimized compilation, then named singleton_default_bytes test; no elimination')
(O/'inputs.json').write_text(json.dumps(record,indent=2)+'\n')
print('expected time: cached optimized compilation then exactly one singleton byte-default execution',flush=True)
r=subprocess.run(cmd,env=env,capture_output=True,text=True);(O/'output.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr)
assert r.returncode==0,r.returncode
assert 'RDCD4_SINGLETON:'+'00'*64 in r.stdout
binaries=[]
for p in (D/'classification-target/release/deps').glob('pv_fscan_deployed_project_fixture-*'):
 if p.is_file() and os.access(p,os.X_OK):binaries.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(O/'result.json').write_text(json.dumps(dict(result='PASS',classification=record['classification'],literal_hex='00'*64,executables=binaries,fixture_sha256=record['fixture_sha256'],lockfile_sha256=record['lockfile_sha256'],allocation='No allocator in the default helper cone. Harness formatting/output allocations occur only after the compared result; their failures remain rdea-1.',compiler='shipped codegen V370/D381/D386 remains; harness uses identical crate sources and exact deployed versions/features/profile'),indent=2)+'\n')
