from NBB_host import *
import hashlib,difflib
# Read-only recovery and source inventory after every owned proof is terminal.
code=f'''from pathlib import Path
import hashlib,json,os
b=Path({B!r});src=b/'NBB_src'
out={{'snapshots':{{}},'source_hashes':{{}},'tools':{{}},'library':{{}},'live_provers':[],'tmp':[]}}
for p in src.rglob('*'):
 if p.is_file():out['source_hashes'][str(p.relative_to(src))]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
for d in b.glob('NBB_K*'):
 if not d.is_dir():continue
 rc=d/'receipt.json'
 if not rc.exists():continue
 r=json.loads(rc.read_text())
 for n in r['sources']:
  p=d/'sources'/n
  assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_hashes'][n]
  out['snapshots'][str(p.relative_to(b))]=p.read_text()
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
 try:argv=(d/'cmdline').read_bytes().decode().split('\\0')
 except (OSError,UnicodeDecodeError):continue
 if not argv or not any({B!r} in arg for arg in argv):continue
 if Path(argv[0]).name in ['lean','lake','cbmc','cargo-kani','kani-driver','kani-compiler','rustc','cargo']:
  out['live_provers'].append(dict(pid=d.name,argv=argv))
for p in (b/'NBB_tmp').rglob('*'):
 if p.is_file():out['tmp'].append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
print(json.dumps(out))
'''
r=py(code);assert r.returncode==0,r.stderr
x=json.loads(r.stdout)
for n,s in x.pop('snapshots').items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert not x['live_provers'],x['live_provers']
expected=json.loads(Path('evidence/leaf-sampler1-20261027/LPk_SOURCE.json').read_text())['file_sha256']
actual=x['source_hashes'];vp='crates/aspis-r1-cost-probe/src/verifier.rs'
native=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+vp],text=True)
marker='\n#[cfg(kani)] #[path="NBB_harness.rs"] mod NBB_harness;\n'
errors=[]
for n,h in expected.items():
 want=hashlib.sha256((native+marker).encode()).hexdigest() if n==vp else h
 if actual.get(n,{}).get('sha256')!=want:errors.append(n)
extras=sorted(set(actual)-set(expected));assert extras==['crates/aspis-r1-cost-probe/src/NBB_harness.rs'],extras
assert not errors,errors
x['frozen_files_checked']=len(expected);x['errors']=errors;x['only_extra']=extras;x['only_frozen_file_difference']='cfg(kani) NBB child registration in scratch verifier.rs'
# Verify actual resolved Aeneas objects, not just an assumed directory.
oldpins=json.loads((E/'NBB_LIBRARY_PIN.json').read_text())
for p in x['library'].values():assert oldpins[p['path']]=={'sha256':p['sha256'],'bytes':p['bytes']},p
x['resolved_library_matches_each_compile_pin']=True
for line in Path('evidence/leaf-p6-11-20261027/LPm_tools.sha256').read_text().splitlines()[:6]:
 h,p=line.split()
 assert x['tools'][p]['sha256']==h,p
x['compiler_and_kani_pins_match_inherited']=True
(E/'NBB_TERMINAL_SOURCE.json').write_text(json.dumps(x,indent=2)+'\n')
# Every native patch reconstructs the exact frozen-source instrumentation.
for p in sorted(E.glob('NBB_K*/receipt.json')):
 d=p.parent;f=d/'sources/NBB_src/crates/aspis-r1-cost-probe/src/NBB_harness.rs'
 harness=f.read_text()
 patch=''.join(difflib.unified_diff(native.splitlines(True),(native+marker).splitlines(True),fromfile='a/'+vp,tofile='b/'+vp))
 patch+=''.join(difflib.unified_diff([],harness.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBB_harness.rs'))
 (d/'NBB_harness.patch').write_text(patch)
print(json.dumps(dict(frozen_files=x['frozen_files_checked'],source_errors=errors,library_objects=len(x['library']),live_provers=x['live_provers'],private_solver_files=len(x['tmp']))))
