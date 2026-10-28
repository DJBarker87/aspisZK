from pathlib import Path
import os,subprocess,json,time,hashlib
H=Path('/home/dombarker/project-offloads/codex-cx-native-sbfstack-20261028');S=H.parent/'codex-cx-lowering2-20261026/src'
env=os.environ.copy();env.update(CARGO_TARGET_DIR=str(H/'NDC_target_native'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='2');env.pop('RUSTFLAGS',None)
print('Time expected in focused optimized core compilation to expose native generic MIR; no arithmetic/proof gate.',flush=True)
cmd=['/home/dombarker/.cargo/bin/cargo','rustc','--release','--locked','--offline','-j','2','--manifest-path',str(S/'Cargo.toml'),'-p','aspis-core','--features','r0','--','--emit=mir,llvm-ir']
t=time.monotonic();q=subprocess.run(cmd,cwd=H,env=env,capture_output=True,text=True);(H/'NDC_core_emit_stderr.txt').write_text(q.stderr)
r={'command':cmd,'exit':q.returncode,'wall':time.monotonic()-t,'outputs':{}}
for p in (H/'NDC_target_native/release/deps').glob('aspis_core*'):
 if p.suffix not in ['.mir','.ll']:continue
 text=p.read_text();hits=[(i+1,l) for i,l in enumerate(text.splitlines()) if 'EncodingDomain' in l and 'encode' in l]
 r['outputs'][p.name]={'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'encoding_domain_encode_lines':hits[:30]}
 if p.suffix=='.mir':
  lines=text.splitlines();ex=[]
  for i,l in enumerate(lines):
   if ('fn ' in l and 'encode' in l and ('EncodingDomain' in l or 'prover' in l)) or ('as CodeField' in l):
    if 'fn ' in l:ex.extend(f'{n+1}: {lines[n]}' for n in range(max(0,i-3),min(len(lines),i+12)))
  (H/'NDC_NATIVE_GENERIC_MIR.txt').write_text('\n'.join(ex)+'\n')
print(q.stderr[-2000:]);print(json.dumps(r));(H/'NDC_NATIVE_EMIT.json').write_text(json.dumps(r,indent=2)+'\n');raise SystemExit(q.returncode)
