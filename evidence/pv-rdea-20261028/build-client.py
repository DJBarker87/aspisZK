from pathlib import Path
import subprocess,json,hashlib,os,sys,time
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028')
S=D.parent/'codex-pv-fscan-20261028/src'
manifest=json.loads((D/'build-source-pins.json').read_text())
checks=[]
for row in manifest['files']:
 p=S/row['path']
 if p.exists():
  actual=hashlib.sha256(p.read_bytes()).hexdigest()
  checks.append(dict(**row,actual=actual,ok=actual==row['sha256']))
# Require all actual project Rust/manifests to be pinned; historical snapshot may lack unrelated docs.
pinned={x['path'] for x in manifest['files']}
extra=[]
for root in ['crates','programs','tools/r1-cost-probe']:
 for p in (S/root).rglob('*'):
  if p.suffix in ['.rs','.toml','.lock'] and 'target' not in p.parts and str(p.relative_to(S)) not in pinned:extra.append(str(p))
r=dict(revision=manifest['revision'],checks=checks,extra=extra,ok=all(x['ok'] for x in checks) and not extra)
(D/'build-source-check.json').write_text(json.dumps(r,indent=2)+'\n')
assert r['ok'],[x for x in checks if not x['ok']]+extra
wrapper=D/'emit-wrapper.py';wrapper.chmod(0o700)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',RUSTC_BOOTSTRAP='1',CARGO_TARGET_DIR=str(D/'client-target'),RUSTC_WRAPPER=str(wrapper))
cmd=['taskset','--cpu-list','0-3','cargo','build','--release','--locked','--manifest-path',str(S/'tools/r1-cost-probe/Cargo.toml'),'-p','aspis-r1-cu-probe','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','devnet_spend','-j','4']
(D/'build-command.json').write_text(json.dumps(dict(command=cmd,env={k:env[k] for k in ['RUSTUP_TOOLCHAIN','RUSTC_BOOTSTRAP','CARGO_TARGET_DIR','RUSTC_WRAPPER']},expected_phase='compilation and LLVM/MIR emission of deployed client, no proof generation or execution',source_revision=manifest['revision'],print_axioms='N/A native compilation'),indent=2)+'\n')
p=subprocess.run(cmd,env=env)
if p.returncode:sys.exit(p.returncode)
b=D/'client-target/release/devnet_spend'
(D/'client-artifact.json').write_text(json.dumps(dict(sha256=hashlib.sha256(b.read_bytes()).hexdigest(),bytes=b.stat().st_size,toolchain=subprocess.check_output(['/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc','-vV'],text=True)),indent=2)+'\n')
