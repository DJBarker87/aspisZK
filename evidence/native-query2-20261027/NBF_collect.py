from NBF_host import *
import hashlib
# Read-only inventory after the last owned proof is terminal.
code=f'''from pathlib import Path
import hashlib,json,os
b=Path({B!r});src=b/'NBF_src'
out={{'source_hashes':{{}},'tools':{{}},'library':{{}},'live_provers':[],'tmp':[]}}
for p in src.rglob('*'):
 if p.is_file():out['source_hashes'][str(p.relative_to(src))]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
for n in ['/home/dombarker/.cargo/bin/cargo-kani','/home/dombarker/.cargo/bin/cargo',
 '/home/dombarker/.kani/kani-0.67.0/bin/kani-driver','/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler',
 '/home/dombarker/.kani/kani-0.67.0/bin/cbmc','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean',
 {B!r}+'/S2W_run_host.py',{B!r}+'/S2W_lean_host.py',
 '/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py']:
 p=Path(n);out['tools'][n]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
roots=['/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027',
 '/home/dombarker/project-offloads/codex-cx-sound-int2-20261025',
 '/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects',
 '/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean']
for root in roots:
 q=Path(root);paths=[q/'Aeneas.olean']+list((q/'Aeneas').rglob('*.olean'))
 for p in paths:
  if not p.is_file():continue
  key=str(p.relative_to(q))
  if key not in out['library']:out['library'][key]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
for d in Path('/proc').iterdir():
 if not d.name.isdigit():continue
 try:
  argv=(d/'cmdline').read_bytes().decode().split('\\0');cwd=str((d/'cwd').resolve())
 except (OSError,UnicodeDecodeError):continue
 if not argv:continue
 own=cwd.startswith({B!r}) or any({B!r} in arg for arg in argv)
 if own and Path(argv[0]).name in ['lean','lake','cbmc','cargo-kani','kani-driver','kani-compiler','rustc','cargo']:
  out['live_provers'].append(dict(pid=d.name,argv=argv,cwd=cwd))
for p in (b/'NBF_tmp').rglob('*'):
 if p.is_file():out['tmp'].append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
print(json.dumps(out))
'''
r=py(code);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);assert not x['live_provers'],x['live_provers']
expected=json.loads(Path('evidence/leaf-sampler1-20261027/LPk_SOURCE.json').read_text())['file_sha256']
actual=x['source_hashes'];errors=[]
markers={'crates/aspis-r1-cost-probe/src/verifier.rs':'\n#[cfg(kani)] #[path="NBF_harness.rs"] mod NBF_harness;\n','crates/aspis-r1-cost-probe/src/candidate.rs':'\n#[cfg(kani)] #[path="NBF_query.rs"] mod NBF_query;\n'}
for n,h in expected.items():
 if n in markers:
  original=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
  h=hashlib.sha256((original+markers[n]).encode()).hexdigest()
 if actual.get(n,{}).get('sha256')!=h:errors.append(n)
extras=sorted(set(actual)-set(expected))
assert extras==['crates/aspis-r1-cost-probe/src/NBF_harness.rs','crates/aspis-r1-cost-probe/src/NBF_query.rs'],extras
assert not errors,errors
x.update(frozen_files_checked=len(expected),errors=errors,only_extra=extras,only_frozen_file_differences='Two cfg(kani)-only NBF child registrations in scratch verifier.rs/candidate.rs')
oldpins=json.loads((E/'NBF_LIBRARY_PIN.json').read_text())
for pin in x['library'].values():assert oldpins[pin['path']]=={'sha256':pin['sha256'],'bytes':pin['bytes']},pin
x['resolved_library_matches_each_compile_pin']=True
for line in Path('evidence/leaf-p6-11-20261027/LPm_tools.sha256').read_text().splitlines()[:6]:
 h,p=line.split();assert x['tools'][p]['sha256']==h,p
for n in ['S2W_run_host.py','S2W_lean_host.py']:
 want=json.loads((E/'NBF_LAUNCHER_INPUTS.json').read_text())[n]
 assert x['tools'][B+'/'+n]['sha256']==hashlib.sha256(want.encode()).hexdigest()
x['compiler_and_kani_pins_match_inherited']=True
x['local_frozen_release_unchanged']=subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates/','programs/','Cargo.lock','Cargo.toml']).returncode==0
assert x['local_frozen_release_unchanged']
(E/'NBF_TERMINAL_SOURCE.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(frozen_files=x['frozen_files_checked'],errors=errors,library_objects=len(x['library']),live_provers=x['live_provers'],private_solver_files=len(x['tmp']))))
