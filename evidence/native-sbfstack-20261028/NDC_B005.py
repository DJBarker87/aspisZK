from pathlib import Path
import subprocess,json,hashlib,os,time
H=Path('/home/dombarker/project-offloads/codex-cx-native-sbfstack-20261028');S=H.parent/'codex-cx-lowering2-20261026/src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock=sha(S/'Cargo.lock');env=os.environ.copy();env.update(CARGO_TARGET_DIR=str(H/'NDC_target_native'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='2');env.pop('RUSTFLAGS',None)
cmd=['/home/dombarker/.cargo/bin/cargo','build','--release','--locked','--offline','-j','2','--manifest-path',str(S/'Cargo.toml'),'-p','aspis-r1-cost-probe','--lib','--features','prover,optimized-terminal']
print('Time expected in optimized native client compilation; no proof generation or elimination. No build of SBF artifacts.',flush=True)
print('COMMAND',json.dumps(cmd),flush=True)
t=time.monotonic();q=subprocess.run(cmd,cwd=H,env=env,capture_output=True,text=True)
(H/'NDC_native_build_stdout.txt').write_text(q.stdout);(H/'NDC_native_build_stderr.txt').write_text(q.stderr)
r={'command':cmd,'exit':q.returncode,'wall_seconds':time.monotonic()-t,'lock_before':lock,'lock_after':sha(S/'Cargo.lock'),'target':env['CARGO_TARGET_DIR'],'feature_request':'prover,optimized-terminal; package defaults retained','offline':True,'source_inputs':{str(p.relative_to(S)):sha(p) for p in (S/'crates').rglob('*') if p.is_file() and p.suffix in ['.rs','.toml']}}
print(q.stdout[-3000:]);print(q.stderr[-6000:]);print(json.dumps({k:v for k,v in r.items() if k!='source_inputs'}),flush=True)
(H/'NDC_NATIVE_BUILD.json').write_text(json.dumps(r,indent=2)+'\n');assert r['lock_before']==r['lock_after'];raise SystemExit(q.returncode)
