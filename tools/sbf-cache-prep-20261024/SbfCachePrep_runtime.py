#!/usr/bin/env python3
"""Public comparison interpreter/module/loaded-DSO reference; no donor access."""
import gzip,hashlib,json,os,pathlib,re,resource,stat,subprocess,sys,tarfile,time,tomllib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));start=time.monotonic();P=pathlib.Path
paths={sys.executable}
for line in P('/proc/self/maps').read_text().splitlines():
    parts=line.split(None,5)
    if len(parts)==6 and parts[5].startswith(('/usr/','/lib/')):paths.add(parts[5])
for m in tuple(sys.modules.values()):
    p=getattr(m,'__file__',None)
    if p and p.startswith(('/usr/','/lib/')):paths.add(p)
rows=[]
for name in sorted(paths):
    p=P(name);assert p.is_file() and p.stat().st_size<100*1024**2
    h=hashlib.sha256()
    with p.open('rb') as f:
        while b:=f.read(1024**2):h.update(b)
    rows.append(dict(path=name,resolved=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest()))
u=resource.getrusage(0)
print(json.dumps(dict(executable=sys.executable,version=sys.version,files=rows,scope='New reference metadata with comparison modules imported; not historical per-operation loaded mappings or compiler loaded-DSO/time-of-use closure',receipt=dict(command=[sys.executable,'-'],exit=0,wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A')),sort_keys=True))
