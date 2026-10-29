"""Small optimized harness link and one direct execution per original root.
No replacement allocator, copied target body, extraction or Kani.
"""
from pathlib import Path
import os,json,hashlib,subprocess,tomllib
D=Path('/home/dombarker/project-offloads/codex-pv-owno-20261029');O=D.parent/'codex-pv-ownd-20261029';F=D.parent/'codex-pv-fscan-20261028/src'
sha=lambda b:hashlib.sha256(b).hexdigest()
def record(p):b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=sha(b))
pins=json.loads((D/'crate-source-pins.json').read_text())
for p in pins['files']:
 b=(F/p['path']).read_bytes();assert sha(b)==p['sha256'] and len(b)==p['size'],p['path']
lib=O/'target/release/deps/libaspis_statement-d9a1a32deb1a9c73.rlib'
assert sha(lib.read_bytes())=='0e0184bcafb0c970d9a2129429578f2fb85e69a844f6e4ddddafbb05f6f5acd0'
prover_fingerprint=O/'target/release/.fingerprint/aspis-prover-e145be5d261f7d57/lib-aspis_prover.json'
assert 'ct-host-prover' in json.loads(prover_fingerprint.read_text())['features']
core_fingerprint=next((O/'target/release/.fingerprint').glob('aspis-core-*/lib-aspis_core.json'))
assert 'ct-host-prover' in json.loads(core_fingerprint.read_text())['features']
print('prover/core ct-host-prover features verified',flush=True)
fingerprint=O/'target/release/.fingerprint/aspis-statement-d9a1a32deb1a9c73/lib-aspis_statement.json'
fp=json.loads(fingerprint.read_text());assert json.loads(fp['features'])==['pool-v1-kernel','r0']
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1')
meta=json.loads(subprocess.check_output(['cargo','metadata','--manifest-path',str(O/'probe/Cargo.toml'),'--locked','--format-version','1'],text=True,env=env))
units=json.loads((O/'deployed-units.json').read_text());expected={}
for u in units:expected.setdefault(u['package_id'],set()).update(u['features'])
nodes={n['id']:n for n in meta['resolve']['nodes']}
lock=tomllib.loads((O/'deployed-client-Cargo.lock').read_text())
allowed={(p['name'],p['version'],p.get('source'),p.get('checksum')) for p in lock['package']}
fixturelock=tomllib.loads((O/'probe/Cargo.lock').read_text())
for p in fixturelock['package']:
 if p['name']=='pv-fscan-deployed-project-fixture':continue
 assert (p['name'],p['version'],p.get('source'),p.get('checksum')) in allowed,p
for p in meta['packages']:
 if p['id'] in expected:assert set(nodes[p['id']]['features'])==expected[p['id']],p['id']
cmd=['rustc','+1.94.1','--edition=2021','-O','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','--extern','aspis_statement='+str(lib),'--extern','aspis_prover='+str(next(lib.parent.glob('libaspis_prover-*.rlib'))),'--extern','aspis_core='+str(next(lib.parent.glob('libaspis_core-*.rlib'))),'-L','dependency='+str(lib.parent),str(D/'harness.rs'),'-o',str(D/'harness')]
print('phase: small optimized harness compilation/link against pinned identical-source deployed-feature rlib; then error-preserving forward helper differential and first-pole checks',flush=True)
q=subprocess.run(cmd,env=env);assert q.returncode==0
runs=[]
for mode in ['consuming-instance']:
 q=subprocess.run([str(D/'harness')],text=True,capture_output=True)
 print(mode,q.stdout,flush=True);assert q.returncode==0,q.stderr
 runs.append(dict(mode=mode,command=[str(D/'harness')],exit=q.returncode,stdout=q.stdout,stderr=q.stderr))
result=dict(command=cmd,toolchain=subprocess.check_output(['rustc','+1.94.1','-Vv'],env=env,text=True),profile='release opt-level3 debug_assertions=false overflow_checks=false panic=unwind; rlib inherited exact deployed unit profile',features=[dict(id=p['id'],features=nodes[p['id']]['features']) for p in meta['packages']],inputs=[record(p) for p in [lib,next(lib.parent.glob('libaspis_prover-*.rlib')),next(lib.parent.glob('libaspis_core-*.rlib')),D/'harness.rs',D/'native.py',core_fingerprint,prover_fingerprint,D/'crate-source-pins.json',fingerprint,O/'deployed-units.json',O/'deployed-client-Cargo.lock',O/'probe/Cargo.lock',O/'probe/Cargo.toml']],binary=record(D/'harness'),runs=runs,identical_crate_sources=dict(files=len(pins['files']),verified=True,root=str(F/'crates/aspis-statement')),compiler_boundary='V370/D381/D386 retained',evidence_class='finite validation of the actual consuming functions and published-transcript factorization; not a universal proof')
(D/'native-result.json').write_text(json.dumps(result,indent=2)+'\n')
