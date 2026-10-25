"""One capture-only byte export; no project imports or runner execution."""
import os, stat, json, hashlib, base64, time, resource, signal
START=time.monotonic()
signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('capture deadline')))
signal.alarm(120)
STAGE='/home/dombarker/project-offloads/codex-cx-resource-rss-go-v3-20261025'
NAMES=['lock.json','scope-argv.json','scope-child.json','scope.stdout','scope.stderr','marker.json',
       'go-controls-before.json','go-controls-after-scan.json','go-control-check.json','go-controls-after.json','go-pins.json']
for action in ('run','go'):
    NAMES += [action+'-'+suffix+'.json' for suffix in ('pre-pins','post-pins','exit','resident-guard','inherited-limits-initial','inherited-limits-final')]
for phase in ('prospective','inside-scope'):
    NAMES += [phase+'-'+suffix+'.json' for suffix in ('ordered','report','metrics')]
assert len(NAMES)==len(set(NAMES))
COUNT=0
OUT=0
def emit(obj):
    global OUT
    raw=json.dumps(obj,separators=(',',':'))+'\n'
    OUT+=len(raw)
    if OUT>400*2**20: raise ValueError('output bound')
    usage=resource.getrusage(resource.RUSAGE_SELF)
    if usage.ru_maxrss*1024>512*2**20: raise MemoryError('own resident bound')
    if time.monotonic()-START>120: raise TimeoutError('capture deadline')
    print(raw,end='',flush=True)
def ident(s):
    return [s.st_dev,s.st_ino,s.st_mode,s.st_uid,s.st_nlink,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
def directory(parent,name):
    return os.open(name,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=parent)
fd=os.open('/',os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
for part in STAGE.strip('/').split('/'):
    new=directory(fd,part);os.close(fd);fd=new
s=os.fstat(fd)
assert s.st_uid==1000 and stat.S_IMODE(s.st_mode)==0o700
emit(dict(kind='stage',path=STAGE,uid=s.st_uid,mode=oct(stat.S_IMODE(s.st_mode)),nosymlink_components=True))
try:
    cap=directory(fd,'capture')
except FileNotFoundError:
    for name in NAMES: emit(dict(kind='absent',name=name,reason='capture directory absent'))
else:
    assert os.fstat(cap).st_uid==1000
    for name in NAMES:
        try: f=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=cap)
        except FileNotFoundError:
            emit(dict(kind='absent',name=name));continue
        try:
            pre=os.fstat(f)
            assert stat.S_ISREG(pre.st_mode) and pre.st_nlink==1 and pre.st_uid==1000
            assert 0<=pre.st_size<=32*2**20
            COUNT+=pre.st_size
            assert COUNT<=256*2**20
            assert ident(os.stat(name,dir_fd=cap,follow_symlinks=False))==ident(pre)
            emit(dict(kind='begin',name=name,stat=ident(pre),size=pre.st_size))
            h=hashlib.sha256();size=0;seq=0
            while True:
                b=os.read(f,min(512*1024,pre.st_size-size+1))
                if not b: break
                size+=len(b)
                assert size<=pre.st_size
                h.update(b)
                emit(dict(kind='chunk',name=name,seq=seq,data=base64.b64encode(b).decode()))
                seq+=1
            assert size==pre.st_size and ident(os.fstat(f))==ident(pre)
            assert ident(os.stat(name,dir_fd=cap,follow_symlinks=False))==ident(pre)
            emit(dict(kind='end',name=name,size=size,sha256=h.hexdigest(),chunks=seq,stable=True))
        finally: os.close(f)
    os.close(cap)
os.close(fd)
u=resource.getrusage(resource.RUSAGE_SELF)
emit(dict(kind='complete',original_bytes=COUNT,wall_seconds=time.monotonic()-START,peak_rss_bytes=u.ru_maxrss*1024,swap=u.ru_nswap,metrics_scope='retrieval helper only; not original run',print_axioms='N/A'))
