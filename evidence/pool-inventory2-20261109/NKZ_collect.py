"""Read-only retention of new release compiler inputs; no build launch."""
from pathlib import Path
import subprocess,json,hashlib,lzma,shlex
E=Path(__file__).resolve().parent;R=E.parents[1];OLD=R/'evidence/pool-inventory-20261109'
F='b936275465600469312d1f058cdc91ea2a11f3dc'; C='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-legacy-removal-20261109/pool2/diagnostics'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(p,rev=F):return subprocess.check_output(['git','show',rev+':'+p],cwd=R)
def put(n,d):(E/n).write_text(json.dumps(d,indent=1,sort_keys=True)+'\n')
base=json.loads((OLD/'NKS_DEPLOYED_BUILD.json').read_text()); receipt=json.loads((R/'evidence/legacy-removal-20261109/NKX_pool2/receipt.json').read_text())
paths=set(subprocess.check_output(['git','ls-tree','-r','--name-only',F],cwd=R,text=True).splitlines())
checks=[];removed=[]
for p in base['compiler_input_checks']:
 if p['path'] not in paths:removed.append(p);continue
 b=git(p['path']); expected=receipt['source_manifest'].get(p['path'],p['expected']); assert sha(b)==expected,p['path']
 checks.append(dict(path=p['path'],expected=expected,actual=sha(b),matches=True,changed_from_NKS=p['actual']!=sha(b)))
assert subprocess.check_output(['git','diff',C,F,'--','crates'],cwd=R)==b''
assert git('Cargo.lock')==git('Cargo.lock',C)
put('NKZ_DEPLOYED_BUILD.json',dict(frozen_revision=F,crates_revision=C,historical_build_revision=receipt['source_revision'],pool_build=receipt,compiler_input_checks=checks,removed_compiler_inputs=removed,lock_sha256=sha(git('Cargo.lock')),feature_warning=base['feature_warning'],provenance='NKX_pool2 exact new ELF; source manifest checked against new freeze. Unchanged core/statement compiler artifacts reused from NKS after all surviving input hash checks.'))
inputs=[]
for crate in ['aspis_pool','aspis_core','aspis_statement']:
 for ext in ['mir.xz','ll.xz','mono.txt','command.json']:
  name='NKZ_'+crate+'.'+ext;out=E/name
  if crate=='aspis_pool':
   remote=B+('/compiler-output/'+crate+'.'+ext.removesuffix('.xz') if ext.endswith('.xz') else '/'+crate+'.'+ext)
   code='import pathlib,lzma,sys;b=pathlib.Path('+repr(remote)+').read_bytes();sys.stdout.buffer.write('+('lzma.compress(b,preset=6)' if ext.endswith('.xz') else 'b')+')'
   if not out.exists():
    with out.open('wb') as f:p=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(code)],stdout=f,stderr=subprocess.PIPE)
    assert p.returncode==0,p.stderr
   origin=remote
  else:out.write_bytes((OLD/name.replace('NKZ_','NKS_')).read_bytes());origin='NKS retained '+name.replace('NKZ_','NKS_')
  b=out.read_bytes();raw=lzma.decompress(b) if ext.endswith('.xz') else b
  if ext.endswith('.xz'):(E/(name.removesuffix('.xz')+'.sha256')).write_text(sha(raw)+'\n')
  inputs.append(dict(path=name,source=origin,sha256=sha(b),uncompressed_sha256=sha(raw),bytes=len(raw)))
put('NKZ_INPUTS.json',dict(frozen_revision=F,crates_revision=C,inputs=inputs,no_build_scopes=True,host_writes_bytes=0,source_validation='All surviving historical compiler inputs checked against NKX build manifest and frozen source; crates and Cargo.lock unchanged.',removed_compiler_input_count=len(removed)))
for n in ['inventory','mir']:(E/('NKZ_NGB_'+n+'_reference.py')).write_bytes((R/'evidence/inv-repair-20261104'/('NGB_'+n+'.py')).read_bytes())
print('NKZ inputs pinned: new release Pool MIR/LLVM/mono, unchanged crate artifacts, no scopes.')
