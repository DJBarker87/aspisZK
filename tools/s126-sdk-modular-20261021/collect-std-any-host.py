#!/usr/bin/env python3
"""Focused source-only std-any packet, including failed extraction boundaries."""
from pathlib import Path
import hashlib,json,shutil,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'std-any-export';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,rel):
 q=O/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
pins=[]
for n in range(1,7):
 tag='std-any-v'+str(n);p=H/tag
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','charon-input.json','aeneas-input.json']:
  if (p/rel).is_file():copy(p/rel,Path(tag)/rel)
 for phase in ['charon','aeneas']:
  for f in (H/'receipts'/(tag+'-'+phase)).glob('*'):
   if f.suffix in ['.json','.log']:copy(f,Path(tag)/'receipts'/phase/f.name)
  admission=H/(tag+'-'+phase+'-admission.json')
  if admission.exists():copy(admission,Path(tag)/admission.name)
 llbc=p/'StdAny.llbc'
 if llbc.exists():
  x=json.loads(llbc.read_text());t=x['translated']
  funs=[]
  for f in t['fun_decls']:
   if not f:continue
   name=str(f['item_meta']['name'])
   if "['any'," in name or "['next'," in name or 'checkpoint_nonzero' in name:
    funs.append(dict(name=f['item_meta']['name'],span=f['item_meta']['span'],body_kind=('opaque' if f['body']=='Opaque' else list(f['body'])[0])))
  pins.append(dict(tag=tag,llbc_sha256=sha(llbc),has_errors=x['has_errors'],reached_functions=funs))
 if n in [5,6]:
  for f in (p/'generated').rglob('*.lean'):
   copy(f,Path(tag)/(str(f.relative_to(p))+'.txt'))
stdlib=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/slice/iter/macros.rs')
copy(stdlib,Path('std')/'aeneas-rust-slice-iter-macros.rs')
kani=H/'kani-rust-slice-iter-macros.rs';copy(kani,Path('std')/kani.name)
def any_body(source):
 s=source.read_text();a=s.index('fn any<F>');b=s.index('{',a);depth=1;i=b+1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
a=any_body(stdlib);k=any_body(kani);assert a==k
(O/'source-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',extraction_parent_revision='9b6ba762d',protocol_freeze='b2727acd3abf79315d18b754a260f58f4b1c6326',stdlib_files={str(p):sha(p) for p in [stdlib,kani]},identical_any_method=True,any_method_sha256=hashlib.sha256(a.encode()).hexdigest(),any_method=a,llbc=pins,qualification='Successful full-MIR physical-layout extraction is v5. v6 opaque-layout Aeneas fails. Pointer carrier/next instantiation remains explicit; no native SDK source closure. Host receipt source_revision d8fc9db names the host workspace base, not an adoption of a different protocol freeze.'),indent=2)+'\n')
for f in ['extract-std-any-host.py','collect-std-any-host.py']:
 copy(H/'kit'/f,Path('runner')/f)
print('focused source-only std any export',O)
