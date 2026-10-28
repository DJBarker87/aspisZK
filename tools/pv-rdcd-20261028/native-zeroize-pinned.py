from pathlib import Path
import json,subprocess,os,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');P=D/'zeroize-fixture';P.mkdir(exist_ok=True)
(P/'Cargo.toml').write_text('''[package]
name="pv-rdcd-zeroize"
version="0.0.0"
edition="2021"
[workspace]
[lib]
path="empty.rs"
[dependencies]
zeroize={version="=1.9.0",features=["alloc","zeroize_derive"]}
unicode-ident="=1.0.24"
syn={version="=2.0.119",features=["extra-traits","full","visit","visit-mut"]}
quote="=1.0.47"
proc-macro2="=1.0.107"
''')
(P/'empty.rs').write_text('')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target'))
rustc='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc';commands=[]
def run(c):
 commands.append(c);r=subprocess.run(c,env=env,capture_output=True,text=True);print(r.stderr,flush=True);assert r.returncode==0,(c,r.stdout,r.stderr);return r.stdout
version=run([rustc,'-vV']);print(version)
a=run(['cargo','build','--offline','--manifest-path',str(P/'Cargo.toml'),'--release','-j','4','--message-format=json'])
(P/'cargo-artifacts.jsonl').write_text(a)
arts=[json.loads(l) for l in a.splitlines() if l.startswith('{')];z=next(x for x in arts if x.get('reason')=='compiler-artifact' and x['target']['name']=='zeroize');assert z['features']==['alloc','default','zeroize_derive'],z
lib=next(x for x in z['filenames'] if x.endswith('.rlib'))
meta=json.loads(run(['cargo','metadata','--offline','--manifest-path',str(P/'Cargo.toml'),'--format-version','1']))
(P/'metadata.json').write_text(json.dumps(meta))
features=[dict(package=n['id'],features=n['features']) for n in meta['resolve']['nodes']]
# Exact deployed graph is retained independently of this focused zeroize-only build.
prior=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/units-client-bin/features.json');deployed=json.loads(prior.read_text())
(D/'deployed-client-features.json').write_text(json.dumps(deployed,indent=2)+'\n')
checks=[]
for name in ['zeroize-native.rs','zeroize-drop.rs']:
 p=D/name;o=P/name.removesuffix('.rs')
 c=[rustc,'-Copt-level=3','-Cdebug-assertions=false','-Coverflow-checks=false','-Cpanic=unwind','--edition=2021',str(p),'--extern','zeroize='+lib,'-L','dependency='+str(Path(lib).parent),'-o',str(o)]
 run(c);out=run([str(o)]);print(out);checks.append(dict(fixture=name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),output=out))
(P/'result.json').write_text(json.dumps(dict(toolchain=version,features=features,deployed_features_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),profile=dict(name='release',opt_level=3,debug_assertions=False,overflow_checks=False,panic='unwind'),commands=commands,checks=checks,evidence_class='finite validation only; byte outputs and destructor observations; no machine non-elision claim'),indent=2)+'\n')
