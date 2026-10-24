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
result=dict(schema='sbf-current-driver-tool-metadata-v1',historical_identity=False)
allowed.append('/home/dombarker/.cargo/bin')
for path in ['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','/home/dombarker/.cache/solana/v1.52/platform-tools/rust/lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld','/home/dombarker/.cache/solana/v1.52/platform-tools/rust/lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld','/home/dombarker/.cargo/bin/cargo','/home/dombarker/.cargo/bin/rustc','/home/dombarker/.rustup/settings.toml']:
 pin(path,path.endswith('.toml'))
q=resolve('/home/dombarker/.rustup/toolchains')
result['global_toolchain_names']=[] if q is None else sorted(p.name for p in q.iterdir())
# Resolve the globally configured default, not any project's rust-toolchain file.
import tomllib
settings=resolve('/home/dombarker/.rustup/settings.toml')
if settings:
 default=tomllib.loads(settings.read_text()).get('default_toolchain')
 result['configured_default']=default
 if default:
  for name in ['cargo','rustc']:
   exe=pin('/home/dombarker/.rustup/toolchains/'+default+'/bin/'+name)
   if exe:
    c=[str(exe),'-V'];tt=time.monotonic();x=subprocess.run(c,capture_output=True,text=True)
    result[name+'_metadata']=dict(command=c,exit=x.returncode,wall_seconds=time.monotonic()-tt,stdout=x.stdout,stderr=x.stderr,classification='metadata only')
u=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN)
result.update(pins=pins,symlinks=links,blocked_lookups=blocked,receipt=dict(command=['python3','-'],exit=0,wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,children_peak_rss_kib=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,print_axioms='N/A: metadata only'))
print(json.dumps(result,indent=2))
