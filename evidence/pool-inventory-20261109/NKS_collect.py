"""Read-only frozen-build input collector. No compiler or prover launch."""
from pathlib import Path
import subprocess,json,hashlib,lzma,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-lowering2-20261026/build-pool-v1/diagnostics'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(p):return subprocess.check_output(['git','show',F+':'+p],cwd=R)
def put(n,d): (E/n).write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
manifest=json.loads(subprocess.check_output(['git','show','HEAD:evidence/lowering2-20261026/Low2_build_manifest.json'],cwd=R))
b=next(b for b in manifest['builds'] if b['mode']=='pool')
checks=[]
for p in b['repository_compiler_inputs']:
 raw=git(p['path']);checks.append(dict(path=p['path'],expected=p['sha256'],actual=sha(raw),matches=sha(raw)==p['sha256']))
assert all(p['matches'] for p in checks),[p for p in checks if not p['matches']]
put('NKS_DEPLOYED_BUILD.json',dict(frozen_revision=F,historical_build_revision=manifest['source_revision'],pool_build=b,compiler_input_checks=checks,lock_sha256=sha(git('Cargo.lock')),feature_warning='Cargo.toml comments default-off do not describe the pinned deployed ELF; compiler invocation features control.'))
inputs=[]
for crate,stem in [('aspis_pool','aspis_pool'),('aspis_core','aspis_core-268c35f57b2871a4'),('aspis_statement','aspis_statement-619c698a69debaf8')]:
 for ext in ['mir','ll']:
  remote=B+'/compiler-output/'+stem+'.'+ext;out=E/('NKS_'+crate+'.'+ext+'.xz')
  if not out.exists():
   code='import pathlib,lzma,sys;sys.stdout.buffer.write(lzma.compress(pathlib.Path('+repr(remote)+').read_bytes(),preset=6))'
   with out.open('wb') as f:r=subprocess.run(['ssh',H,'python3 -c '+__import__('shlex').quote(code)],stdout=f,stderr=subprocess.PIPE)
   assert r.returncode==0,r.stderr
  raw=lzma.decompress(out.read_bytes());(E/(out.name.removesuffix('.xz')+'.sha256')).write_text(sha(raw)+'\n')
  inputs.append(dict(path=out.name,host_source=remote,sha256=sha(out.read_bytes()),uncompressed_sha256=sha(raw),bytes=len(raw)))
 for ext in ['mono.txt','command.json']:
  remote=B+'/'+crate+'.'+ext;out=E/('NKS_'+crate+'.'+ext)
  if not out.exists():out.write_bytes(subprocess.check_output(['ssh',H,'cat '+__import__('shlex').quote(remote)]))
  inputs.append(dict(path=out.name,host_source=remote,sha256=sha(out.read_bytes()),bytes=out.stat().st_size))
put('NKS_INPUTS.json',dict(frozen_revision=F,inputs=inputs,no_build_scopes=True,source_validation='All 133 historical Pool compiler repository inputs match the frozen revision byte hashes.',host_writes_bytes=0))
for n in ['inventory','mir']:
 src=R/'evidence/inv-repair-20261104'/('NGB_'+n+'.py');(E/('NKS_NGB_'+n+'_reference.py')).write_bytes(src.read_bytes())
print('NKS retained deployed SBF MIR, LLVM and monomorphized instances; 133 frozen input hashes agree.')
