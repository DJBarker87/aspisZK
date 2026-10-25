#!/usr/bin/env python3
"""Unprivileged own-stage/path/tool-version and comparison-runtime metadata."""
import hashlib,json,os,pathlib,resource,stat,subprocess,sys,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));start=time.monotonic();P=pathlib.Path
STAGE=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024')
def sha(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        while b:=f.read(1024**2):h.update(b)
    return h.hexdigest()
def metadata(p):
    s=p.lstat();acl={}
    for name in os.listxattr(p,follow_symlinks=False):
        if name.startswith('system.posix_acl_'):
            b=os.getxattr(p,name,follow_symlinks=False);acl[name]=dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
    return dict(path=str(p),uid=s.st_uid,gid=s.st_gid,mode=oct(stat.S_IMODE(s.st_mode)),type=stat.S_IFMT(s.st_mode),symlink=stat.S_ISLNK(s.st_mode),acl=acl)
paths=[STAGE]+[P('/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023')/s for s in ('sbf-target-verifier','sbf-target-pool')]
rows=[]
for p in paths:
    chain=[metadata(x) for x in reversed((p,*p.parents))]
    assert all(not x['symlink'] for x in chain),'path escape/link denies'
    rows.append(dict(root=str(p),chain=chain,resolved=str(p.resolve(strict=True))))
assert STAGE.stat().st_uid==os.getuid()==1000 and stat.S_IMODE(STAGE.stat().st_mode)==0o700
assert (STAGE/'OWNER').read_text()=='SbfRecapturePrep 20261024\n'
pins={}
for name,want in [('source-inputs.json','a84a528cfc4b294c603fe5381343cdaf9df0547467bcc94e61a67e5111adb9d1'),('src/Cargo.lock','5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'),('rustc-diagnostics.py','fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84')]:
    p=STAGE/name;assert not p.is_symlink() and p.is_file();actual=sha(p);assert actual==want;pins[name]=dict(sha256=actual,bytes=p.stat().st_size)
cargo=P('/home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin/cargo')
assert sha(cargo)=='b4171a5b807c0d54cd02fe2ca2ae9505d6bd1c9c8d1d8b23e5189de9abdd4f98'
cmd=[str(cargo),'-V'];t=time.monotonic();query=subprocess.run(cmd,capture_output=True,timeout=10);assert query.returncode==0
# Hash only own interpreter/loaded public runtime modules, never unrelated proc
# mappings. No dynamic loader tool or compiler is executed.
loaded=set()
for line in P('/proc/self/maps').read_text().splitlines():
    parts=line.split(None,5)
    if len(parts)==6 and parts[5].startswith(('/usr/','/lib/')):loaded.add(parts[5])
for module in tuple(sys.modules.values()):
    p=getattr(module,'__file__',None)
    if p and p.startswith(('/usr/','/lib/')):loaded.add(p)
loaded.add(sys.executable)
runtime=[]
for name in sorted(loaded):
    p=P(name);assert p.is_file() and p.stat().st_size<100*1024**2
    runtime.append(dict(path=name,resolved=str(p.resolve()),sha256=sha(p),bytes=p.stat().st_size))
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
print(json.dumps(dict(paths=rows,stage_pins=pins,cache_entered=False,stage_created=False,space=os.statvfs(STAGE).f_bavail*os.statvfs(STAGE).f_frsize,cargo_query=dict(command=cmd,exit=query.returncode,stdout=query.stdout.decode(),stderr=query.stderr.decode(),wall_seconds=time.monotonic()-t,classification='version query only'),runtime=runtime,receipt=dict(command=[sys.executable,'-'],exit=0,wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,children_peak_rss_kib=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,print_axioms='N/A')),sort_keys=True))
