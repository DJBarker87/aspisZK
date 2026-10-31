from pathlib import Path
import subprocess,os,json,hashlib
B=Path(__file__).resolve().parent;S=B/'NEG_isolated';source=S/'src/lib.rs'
text=source.read_text();marker='\n#[cfg(test)] #[path="../../NEG_native_tests.rs"] mod NEG_native_tests;\n'
if marker not in text:source.write_text(text+marker)
cmd=['/home/dombarker/.cargo/bin/cargo','test','--release','--offline','--manifest-path',str(S/'Cargo.toml'),'--features','private-leaf-salts,optimized-terminal,program-build','-j','1','--lib','NEG_shared','--','--nocapture']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_TARGET_DIR=str(B/'NEG_extract_target'),CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1'+(' --cfg NEG_wrong_native' if os.environ.get('NEG_WRONG')=='1' else ''))
print(json.dumps(dict(command=cmd,rustflags=env['RUSTFLAGS'],source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),expected_time='Optimized compilation of isolated unchanged bodies, then bounded differential tests; no elimination or proof generation')),flush=True)
meta=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--locked','--offline','--format-version','1','--manifest-path',str(S/'Cargo.toml'),'--features','private-leaf-salts,optimized-terminal,program-build'],cwd=S,env=env,capture_output=True,text=True)
assert meta.returncode==0,meta.stderr
(B/'NEG_NATIVE_METADATA.json').write_text(meta.stdout)
r=subprocess.run(cmd,cwd=S,env=env);raise SystemExit(r.returncode)
