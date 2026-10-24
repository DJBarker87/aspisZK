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
root='/home/dombarker/.rustup/toolchains/1.89.0-sbpf-solana-v1.52'
r=resolve(root); result=dict(schema='sbf-current-global-metadata-v1',historical_identity=False,root=root)
if r:
 result['toolchain_resolved']=str(r);result['top_level']=sorted(p.name for p in r.iterdir())
 for rel in ['bin/rustc','bin/cargo','rust-toolchain.toml','version.md','rust-installer-version','lib/rustlib/manifest-rustc','lib/rustlib/manifest-rust-std-sbpf-solana-solana','lib/rustlib/components','lib/rustlib/rustc-src/rust/Cargo.lock']:
  pin(r/rel,not rel.startswith('bin/'))
 for base,pattern in [('lib','librustc*'),('lib/rustlib/sbpf-solana-solana/lib','libcore*'),('lib/rustlib/sbpf-solana-solana/lib','liballoc*'),('lib/rustlib','manifest-*')]:
  d=resolve(r/base)
  if d:
   for p in sorted(d.glob(pattern)):pin(p,base=='lib/rustlib')
 result['rustlib_entries']=sorted(p.name for p in (r/'lib/rustlib').iterdir()) if resolve(r/'lib/rustlib') else []
 for rel in ['lib/rustlib/src','lib/rustlib/src/rust','lib/rustlib/rustc-src']:
  q=resolve(r/rel);result[rel]=None if q is None else dict(resolved=str(q),entries=sorted(p.name for p in q.iterdir()) if q.is_dir() else [])
 exe=resolve(r/'bin/rustc')
 if exe:
  result['queries']=[]
  for args in [['-vV'],['--print','sysroot']]:
   t=time.monotonic();c=[str(exe),*args];x=subprocess.run(c,capture_output=True,text=True)
   result['queries'].append(dict(command=c,classification='metadata only; no compilation/codegen',exit=x.returncode,wall_seconds=time.monotonic()-t,stdout=x.stdout,stderr=x.stderr))
# Only global packaging roots: list names, do not enter unrelated packages or keys.
result['packaging_roots']={}
for base in allowed[1:]:
 q=resolve(base)
 result['packaging_roots'][base]=None if q is None else dict(resolved=str(q),entries=sorted(p.name for p in q.iterdir()))
u=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN)
result.update(pins=pins,symlinks=links,blocked_lookups=blocked,receipt=dict(command=['python3','-'],exit=0,wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,children_peak_rss_kib=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,print_axioms='N/A: metadata only'))
print(json.dumps(result,indent=2))
