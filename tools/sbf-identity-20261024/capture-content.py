#!/usr/bin/env python3
"""Read-only global metadata; never compile or traverse private toolchain links."""
import os,sys,json,hashlib,stat,time,resource,subprocess
from pathlib import Path
start=time.monotonic(); links=[];blocked=[];pins={}
allowed=['/home/dombarker/.rustup','/home/dombarker/.cache/solana','/home/dombarker/.cache/agave','/home/dombarker/.local/share/solana']
def resolve(p):
 p=os.path.normpath(str(p)); todo=p.split('/')[1:];cur='/';n=0
 while todo:
  cur=os.path.join(cur,todo.pop(0))
  try:s=os.lstat(cur)
  except FileNotFoundError:return None
  if stat.S_ISLNK(s.st_mode):
   target=os.readlink(cur); full=os.path.normpath(os.path.join(os.path.dirname(cur),target));links.append(dict(path=cur,target=target,resolved_target=full))
   if not any(full==a or full.startswith(a+'/') for a in allowed):
    blocked.append(dict(path=cur,target=full));return None
   n+=1
   if n>30:raise RuntimeError('symlink cycle')
   todo=full.split('/')[1:]+todo;cur='/'
 return Path(cur)
def pin(p,text=False):
 q=resolve(p)
 if q is None:return None
 if not q.is_file():return None
 h=hashlib.sha256();size=0
 with q.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b);size+=len(b)
 row=dict(resolved=str(q),sha256=h.hexdigest(),bytes=size,mode=oct(q.stat().st_mode & 0o777),mtime_ns=q.stat().st_mtime_ns)
 if text and size<100000:row['text']=q.read_text(errors='replace')
 pins[str(p)]=row;return q
root=Path('/home/dombarker/.cache/solana/v1.52')
result=dict(schema='sbf-current-content-manifest-v1',historical_identity=False,root=str(root))
result['packaging_entries']={}
for rel in ['', 'platform-tools', 'platform-tools/rust/bin', 'platform-tools/rust/lib', 'platform-tools/llvm/bin']:
 q=resolve(root/rel)
 if q: result['packaging_entries'][rel]=[dict(name=p.name,symlink=p.is_symlink(),bytes=p.lstat().st_size) for p in sorted(q.iterdir())]
# Hash all rust-src bytes, selected target sysroot and compiler runtime/tool files.
for rel in ['platform-tools/rust/lib/rustlib/src/rust','platform-tools/rust/lib/rustlib/sbpf-solana-solana/lib','platform-tools/rust/bin']:
 q=resolve(root/rel)
 if q:
  for d,dirs,files in os.walk(q,followlinks=False):
   for name in dirs[:]:
    if Path(d,name).is_symlink():resolve(Path(d,name));dirs.remove(name)
   for name in sorted(files):pin(Path(d,name))
q=resolve(root/'platform-tools/rust/lib')
if q:
 for p in sorted(q.iterdir()):
  if p.is_file() or p.is_symlink():pin(p)
for rel in ['platform-tools/version.md','platform-tools/version.txt','platform-tools/llvm/bin/clang','platform-tools/llvm/bin/ld.lld','platform-tools/llvm/bin/llvm-objcopy','platform-tools/llvm/bin/llvm-readelf']:
 pin(root/rel,rel.endswith(('.txt','.md')))
for p in sorted(root.iterdir()):
 if p.is_file():pin(p, p.suffix in ('.txt','.json','.md'))
# Read only explicit source declarations and Cargo.lock, not arbitrary fixtures.
src=root/'platform-tools/rust/lib/rustlib/src/rust'
result['selected_source']={}
for rel in ['Cargo.lock','library/alloc/src/alloc.rs','library/alloc/src/raw_vec/mod.rs','library/alloc/src/vec/mod.rs','library/core/src/array/mod.rs','library/core/src/clone.rs','library/core/src/alloc/layout.rs','library/alloc/Cargo.toml','library/core/Cargo.toml']:
 q=resolve(src/rel)
 if q and q.is_file():result['selected_source'][rel]=dict(sha256=pins[str(q)]['sha256'],bytes=pins[str(q)]['bytes'])
u=resource.getrusage(resource.RUSAGE_SELF)
result.update(pins=pins,symlinks=links,blocked_lookups=blocked,receipt=dict(command=['python3','-'],exit=0,wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A: metadata only'))
print(json.dumps(result,indent=2))
