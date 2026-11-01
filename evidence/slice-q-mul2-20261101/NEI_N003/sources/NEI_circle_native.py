from pathlib import Path
import subprocess,os,json,hashlib
B=Path(__file__).resolve().parent
mini=B/'NEI_native_line';(mini/'src').mkdir(parents=True,exist_ok=True)
(mini/'Cargo.toml').write_text('[package]\nname="nei_native_circle"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[dependencies]\naspis-core={path="../NEI_src/crates/aspis-core",features=["r0"]}\n')
(mini/'src/lib.rs').write_bytes((B/'NEI_circle_native.rs').read_bytes())
frozen=json.loads((B/'NEI_FROZEN.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source_pins={}
for n,t in frozen.items():
 if n.startswith('crates/aspis-core/') and n.endswith(('.rs','.toml')):
  p=B/'NEI_src'/n
  assert p.read_text()==t,n
  source_pins[n]=sha(p)
lock_before=sha(B/'NEI_src/Cargo.lock')
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NEI_extract_target'),RUSTFLAGS='-C link-arg=-Wl,--threads=1',CARGO_NET_OFFLINE='true')
cmd=['/home/dombarker/.cargo/bin/cargo','test','--release','--offline','--manifest-path',str(mini/'Cargo.toml'),'-j','1','NEI_circle_differential','--','--exact','--nocapture']
print(json.dumps(dict(command=cmd,expected_time='Optimized compilation, then six tiny frozen-circle/native-emitted fidelity cases; not a proof or arithmetic release gate')),flush=True)
r=subprocess.run(cmd,env=env,cwd=B)
meta=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--offline','--format-version','1','--manifest-path',str(mini/'Cargo.toml')],env=env,capture_output=True,text=True)
(B/'NEI_NATIVE_METADATA.json').write_text(meta.stdout);print(meta.stderr,flush=True)
assert meta.returncode==0
lock_after=sha(B/'NEI_src/Cargo.lock');assert lock_before==lock_after
md=json.loads(meta.stdout)
features={p['id']:p['features'] for p in md['resolve']['nodes']}
assert sorted(features.values(),key=len)==[[],['r0']],features
(B/'NEI_NATIVE_PINS.json').write_text(json.dumps(dict(source_pins=source_pins,features=features,lock_before=lock_before,lock_after=lock_after,qualification='Isolated exact frozen circle-body fidelity fixture with actual frozen aspis-core; no deployed verifier-native contract claimed'),indent=2))
raise SystemExit(r.returncode)
