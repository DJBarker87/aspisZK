from pathlib import Path
import subprocess,os,json,hashlib
B=Path(__file__).resolve().parent;S=B/'NEI_src';frozen=json.loads((B/'NEI_FROZEN.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert (S/'Cargo.lock').read_text()==frozen['Cargo.lock'],'STOP lock drift'
name='crates/aspis-core/src/field/wide_exact.rs';extra=(B/'NEI_field_native.rs').read_text();source_pins={}
for n,t in frozen.items():
 if not n.startswith('crates/aspis-core/'):continue
 p=S/n;desired=t+'\n'+extra if n==name else t
 if p.is_symlink():p.unlink()
 if p.read_text()!=desired:p.write_text(desired)
 source_pins[n]=hashlib.sha256(t.encode()).hexdigest()
inputs=json.loads((B/'NEI_FIELD_TEST_INPUTS.json').read_text())
for n,item in inputs.items():
 assert hashlib.sha256(item['text'].encode()).hexdigest()==item['sha256']
 p=S/n;p.parent.mkdir(parents=True,exist_ok=True)
 if not p.exists() or p.read_text()!=item['text']:p.write_text(item['text'])
lock_before=sha(S/'Cargo.lock');env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NEI_field_native_target'),RUSTFLAGS='-C link-arg=-Wl,--threads=1',CARGO_NET_OFFLINE='true')
cmd=['/home/dombarker/.cargo/bin/cargo','test','--manifest-path',str(S/'crates/aspis-core/Cargo.toml'),'--locked','--offline','--release','--package','aspis-core','--no-default-features','--features','r0','--lib','-j','1','NEI_field_','--','--nocapture']
print(json.dumps(dict(command=cmd,expected_time='Optimized compilation followed by 20 tiny native/emitted differential tests; no universal native claim or arithmetic release gate')),flush=True)
r=subprocess.run(cmd,env=env,cwd=B)
assert (S/name).read_text()==frozen[name]+'\n'+extra
for n in source_pins:
 if n!=name:assert sha(S/n)==source_pins[n],('frozen core drift',n)
lock_after=sha(S/'Cargo.lock');assert lock_before==lock_after
(B/'NEI_NATIVE_PINS.json').write_text(json.dumps(dict(source_pins=source_pins,lock_before=lock_before,lock_after=lock_after,core_features=['r0'],frozen_test_inputs={n:i['sha256'] for n,i in inputs.items()},field_test_sha256=sha(B/'NEI_field_native.rs'),qualification='Native differential fixtures only; all frozen core bytes unchanged except an exact cfg(test) append in own scratch; generic proof uses actual E001 definitions'),indent=2))
raise SystemExit(r.returncode)
