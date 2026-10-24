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
root=Path('/home/dombarker/.cache/solana/v1.52/platform-tools/rust/lib/rustlib/src/rust')
result=dict(schema='sbf-current-source-git-blobs-v1',historical_identity=False,files=[])
q=resolve(root)
for d,dirs,files in os.walk(q,followlinks=False):
 for name in dirs[:]:
  if Path(d,name).is_symlink():resolve(Path(d,name));dirs.remove(name)
 for name in sorted(files):
  p=resolve(Path(d,name))
  if not p:continue
  b=p.read_bytes();result['files'].append(dict(path=str(p.relative_to(root)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),git_blob_sha1=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),mode=oct(p.stat().st_mode & 0o777)))
result['snapshot_metadata']={}
# Named released S10 snapshot only; no private build caches/source traversal.
snap=Path('/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023')
allowed.append(str(snap))
s=resolve(snap)
if s:
 result['snapshot_top_level']=sorted(p.name for p in s.iterdir())
 for name in result['snapshot_top_level']:
  if any(word in name.lower() for word in ['toolchain','sysroot','provenance','manifest','source-inputs','snapshot-exclusions']):
   p=s/name
   if p.is_file():pin(p,True)
u=resource.getrusage(resource.RUSAGE_SELF)
result.update(pins=pins,symlinks=links,blocked_lookups=blocked,receipt=dict(command=['python3','-'],exit=0,wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A: metadata only'))
print(json.dumps(result,indent=2))
