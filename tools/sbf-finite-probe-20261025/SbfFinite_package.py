if __name__ == '__main__':
    raise SystemExit('SbfFinite SOURCE ONLY: disabled before imports')
"""Fixed finite package. Operational data is a later review input, not approval
of the full Producer runtime. Bootstrap source identity remains an external gate.
"""
import hashlib
import json
import os
import stat
import time
from SbfFiniteLinux_capture import (require, identity, inode, canonical,
    open_safe_ancestry, check_entry, FILE_FLAGS, DIR_FLAGS)
from SbfFinite_fixed import PACKAGE, ROOT, OWN, ENV, RUNTIME
UNIT='SbfFinite-20261025-tiny-v1'
ROOT_JOURNAL=OWN+'/journal-root'
USER_JOURNAL='/home/dombarker/SbfFinite-20261025-v1-journal'
LAUNCHER='/usr/local/libexec/SbfFinite-20261025-tiny-root'
SUDO=('/usr/bin/sudo','-n','--',LAUNCHER)
SCOPE=('/usr/bin/systemd-run','--user','--scope','--unit='+UNIT,
       '-p','MemoryHigh=768M','-p','MemoryMax=1G','-p','MemorySwapMax=0','-p','TasksMax=64',
       '/usr/bin/env','-i','HOME=/probe','LC_ALL=C','PATH=/usr/bin','TMPDIR=/tmp',
       '/usr/bin/python3','-I','-S','-B',PACKAGE+'/SbfFinite_user_entry.py')
# Later separately reviewed finite operational publication; NOT Producer RUNTIME_PIN.
OPERATIONAL_PIN=()

def digest(raw):return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))

def pinned_file(path,pin,mode,api=os,ancestry=open_safe_ancestry):
    parent=ancestry(path.rsplit('/',1)[0]);fd=None
    try:
        fd=api.open(canonical(path)[-1],FILE_FLAGS,dir_fd=parent)
        s=api.fstat(fd)
        require(stat.S_ISREG(s.st_mode) and s.st_uid==s.st_gid==0 and s.st_nlink==1 and
                stat.S_IMODE(s.st_mode)==mode and s.st_size==pin['size']<=64*2**20,'pinned file rights/size')
        chunks=[];n=0
        while True:
            b=api.read(fd,min(65536,pin['size']-n+1))
            if not b:break
            n+=len(b);require(n<=pin['size'],'pinned file growth');chunks.append(b)
        raw=b''.join(chunks)
        require(identity(s)==identity(api.fstat(fd)) and digest(raw)==pin,'pinned file drift/hash')
        check_entry(parent,canonical(path)[-1],fd) if api is os else api.check_entry(parent,canonical(path)[-1],fd)
        return raw
    finally:
        if fd is not None:api.close(fd)
        api.close(parent)

def no_duplicates(pairs):
    result={}
    for k,v in pairs:
        require(k not in result,'duplicate JSON key');result[k]=v
    return result

def approval():
    """Fresh fixed finite operational inputs, not full Producer adoption.

    No report/manifest/path/GO argument. This job publishes no such actual host
    data. A later reviewed source revision must pin it; CLI still always denies.
    """
    require(type(OPERATIONAL_PIN) is dict and set(OPERATIONAL_PIN)=={'size','sha256'},'finite operational data not published')
    raw=pinned_file(PACKAGE+'/SbfFinite-operational.json',OPERATIONAL_PIN,0o444)
    value=json.loads(raw,object_pairs_hook=no_duplicates,parse_constant=lambda _:require(False,'nonfinite JSON'))
    require(type(value) is dict and set(value)=={'schema','host','roles','scope_path','limits','env'},'finite operational fields')
    require(value['schema']=='SbfFinite-operational-v1' and value['env']==ENV,'finite operational schema/env')
    require(set(value['roles'])=={'collector','sudo','sudo-monitor','helper'} and
            set(value['host'])==set(value['limits'])=={'collector','helper'},'finite operational roles')
    require(value['scope_path'].startswith('/') and value['scope_path'].endswith('/'+UNIT+'.scope') and
            '..' not in value['scope_path'].split('/'),'finite own scope')
    # Runtime is independently literal candidate data, never caller authority.
    return dict(value,runtime=RUNTIME)

def verify_package():
    from SbfFinite_package_pins import FILES
    require(FILES and all(n.startswith('SbfFinite') and '/' not in n for n in FILES),'fixed package inventory')
    result={n:digest(pinned_file(PACKAGE+'/'+n,r,0o444)) for n,r in sorted(FILES.items())}
    from SbfFinite_launcher_pin import LAUNCHER_PIN
    result[LAUNCHER]=digest(pinned_file(LAUNCHER,LAUNCHER_PIN,0o555))
    # package_pins itself is an explicit bootstrap boundary. Exact externally
    # published install inventory pins it; this function cannot prove its selfpin.
    return result

def verify_tree(rootfd):
    """Exact finite installed guest tree. Bounded expected entries, no discovery.

    SourceFD bytes are rehashed before mount; historical source inode identity
    does not become destination inode identity. No writer authority retained.
    """
    from SbfFinite_validate import validate_fixed
    validate_fixed();anchor=open_safe_ancestry(ROOT)
    try:require(inode(os.fstat(anchor))==inode(os.fstat(rootfd)),'fixed installed root identity')
    finally:os.close(anchor)
    expected={'/':set()};modes={}
    for r in RUNTIME['files']:
        parts=canonical(r['logical']);path='/'
        for i,name in enumerate(parts):
            expected.setdefault(path,set()).add(name)
            nxt=path.rstrip('/')+'/'+name
            if i<len(parts)-1:expected.setdefault(nxt,set())
            else:modes[nxt]=r
            path=nxt
    for target in ('tmp','proc','dev'):
        expected['/'].add(target);expected['/'+target]=set()
    started=time.monotonic();fds={'/':os.dup(rootfd)}
    try:
        for path in sorted(expected,key=lambda p:(p.count('/'),p)):
            require(time.monotonic()-started<110,'tree verification deadline')
            if path!='/':
                parent,name=path.rsplit('/',1);fds[path]=os.open(name,DIR_FLAGS,dir_fd=fds[parent or '/'])
            fd=fds[path];s=os.fstat(fd)
            require(stat.S_ISDIR(s.st_mode) and s.st_uid==s.st_gid==0 and stat.S_IMODE(s.st_mode)==0o555,'sealed directory')
            require(set(os.listdir(fd))==expected[path],'unknown/missing installed entry')
        for path,r in modes.items():
            require(time.monotonic()-started<110,'tree hash deadline')
            pinned_file(ROOT+path,{k:r[k] for k in ('size','sha256')},r['mode'])
    finally:
        for fd in reversed(list(fds.values())):os.close(fd)

def journal(name,value):
    require(name in {'inside-scope-ordered.json','inside-scope-report.json','inside-scope-metrics.json',
                    'root-before.json','root-after.json','user-before.json','user-after.json',
                    'user-guard.json','root-result.json','failure.json'},'fixed journal name')
    if os.geteuid()==0:parent=open_safe_ancestry(ROOT_JOURNAL)
    else:
        parent=os.open(USER_JOURNAL,DIR_FLAGS);s=os.fstat(parent)
        if s.st_uid!=os.getuid() or s.st_gid!=os.getgid() or stat.S_IMODE(s.st_mode)!=0o700:
            os.close(parent);raise RuntimeError('user journal rights')
    fd=None
    try:
        fd=os.open(name,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW|os.O_CLOEXEC,0o600,dir_fd=parent)
        total=0
        for text in json.JSONEncoder(sort_keys=True).iterencode(value):
            raw=text.encode();total+=len(raw);require(total<=128*2**20,'raw capture bound')
            while raw:
                n=os.write(fd,raw);require(n>0,'capture write');raw=raw[n:]
        os.fsync(fd)
    finally:
        if fd is not None:os.close(fd)
        os.close(parent)

def public_summary(value):
    raw=(json.dumps(value,sort_keys=True)+'\n').encode('ascii')
    require(len(raw)<=4*2**20,'transport summary bound')
    return raw
