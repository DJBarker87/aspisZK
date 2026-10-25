"""Finite candidate DATA acquisition; never a pin approval or execution grant."""
import hashlib
import json
import os
from pathlib import Path
import posixpath
import stat
import sys
import sysconfig
import time
from FinalNativeGate_bounded import Reader, CatalogError, stamp

ENTRY_LIMIT=32768
FILE_LIMIT=256*2**20
BYTE_LIMIT=2*2**30
ALIAS_LIMIT=32
MAPS_LIMIT=2**20
STAGE='/home/dombarker/final-native-gate-v8-20261025'
ADMITTED=(STAGE,'/usr/bin','/usr/lib','/usr/lib64','/usr/local/lib','/lib','/lib64','/run/user',
          '/home/dombarker/.kani','/home/dombarker/.rustup','/home/dombarker/.cargo/bin',
          '/home/dombarker/.cargo/registry/src',
          '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')


def admit(path):
    return any(path==r or path.startswith(r+'/') for r in ADMITTED)


class Acquisition:
    def __init__(self,deadline):
        self.deadline=deadline;self.rows={};self.files=set();self.unresolved=[];self.bytes=0
        self.expanded=set()

    def tick(self):
        if time.monotonic()>self.deadline:raise CatalogError('full collection deadline')

    def record(self,path,s):
        self.tick()
        kind='dir' if stat.S_ISDIR(s.st_mode) else 'file' if stat.S_ISREG(s.st_mode) else 'link' if stat.S_ISLNK(s.st_mode) else 'unknown'
        row=dict(kind=kind,uid=s.st_uid,gid=s.st_gid,mode=s.st_mode,stamp=list(stamp(s)))
        if kind=='file':
            if s.st_size>FILE_LIMIT:raise CatalogError('stat per-file256MiB bound BEFORE hash')
            row['size']=s.st_size
        if path in self.rows:
            prior=self.rows[path]
            if any(prior[k]!=v for k,v in row.items()):raise CatalogError('component changed during acquisition: '+path)
            return prior
        if len(self.rows)>=ENTRY_LIMIT:raise CatalogError('finite component32768 bound')
        if kind=='file':
            self.bytes+=s.st_size
            if self.bytes>BYTE_LIMIT:raise CatalogError('stat total2GiB bound BEFORE hash')
        if kind=='unknown' or (kind!='link' and s.st_mode&0o022):
            self.unresolved.append(dict(path=path,reason='type/permissions require review; excluded from hashing'))
        self.rows[path]=row
        return row

    def resolve(self,path):
        """Component-relative O_NOFOLLOW opens; explicit bounded link expansion."""
        if not path.startswith('/') or posixpath.normpath(path)!=path or path.startswith('//'):raise CatalogError('noncanonical candidate path')
        seen=set();pending=path
        while True:
            self.tick();fd=os.open('/',os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
            try:
                self.record('/',os.fstat(fd));parts=[] if pending=='/' else pending.split('/')[1:];current='';restart=False
                for i,name in enumerate(parts):
                    current+='/'+name
                    s=os.stat(name,dir_fd=fd,follow_symlinks=False);e=self.record(current,s)
                    if e['kind']=='link':
                        if current in seen or len(seen)>=ALIAS_LIMIT:raise CatalogError('candidate alias cycle/bound')
                        seen.add(current);target=os.readlink(name,dir_fd=fd)
                        if 'target' in e and e['target']!=target:raise CatalogError('alias target drift')
                        e['target']=target
                        base=target if target.startswith('/') else posixpath.join(posixpath.dirname(current),target)
                        pending=posixpath.normpath(posixpath.join(base,*parts[i+1:]))
                        if not admit(pending):
                            self.unresolved.append(dict(path=path,link=current,target=pending,reason='resolved target outside finite admitted roots'))
                            return None
                        if stamp(os.stat(name,dir_fd=fd,follow_symlinks=False))!=stamp(s):raise CatalogError('alias read race')
                        restart=True;break
                    if e['kind']=='unknown' or s.st_mode&0o022:return None
                    sub=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK|(os.O_DIRECTORY if e['kind']=='dir' else 0),dir_fd=fd)
                    if stamp(os.fstat(sub))!=stamp(s):os.close(sub);raise CatalogError('candidate component open race')
                    os.close(fd);fd=sub
                if not restart:return pending
            finally:os.close(fd)

    def add(self,path,recurse=False):
        if not admit(path):
            self.unresolved.append(dict(path=path,outcome='excluded',reason='candidate path outside fixed root admission; no read'))
            return
        try:canonical=self.resolve(path)
        except FileNotFoundError:
            self.unresolved.append(dict(path=path,outcome='observed_missing',reason='missing candidate role (ENOENT during admitted resolution)'));return
        if canonical is None:
            self.unresolved.append(dict(path=path,outcome='rejected',reason='candidate not acquired; ancestor/type/alias policy rejection, absence not established'))
            return
        e=self.rows[canonical]
        if e['kind']=='file':self.files.add(path);return
        if not recurse or canonical in self.expanded:return
        # Only explicitly selected root directories and their REAL directories
        # recurse. A directory symlink encountered below a root is DATA only.
        self.expanded.add(canonical)
        with Reader(self.catalog()).opened(canonical) as (fd,_,_):
            names=[]
            with os.scandir(fd) as it:
                for item in it:
                    self.tick();names.append(item.name)
                    if len(names)+len(self.rows)>ENTRY_LIMIT:raise CatalogError('directory entry bound')
            self.rows[canonical]['children']=sorted(names)
            for name in sorted(names):
                child=canonical.rstrip('/')+'/'+name
                s=os.stat(name,dir_fd=fd,follow_symlinks=False)
                kind=self.record(child,s)['kind']
                if kind=='link':
                    resolved=self.resolve(child)
                    if resolved and self.rows[resolved]['kind']=='file':self.files.add(child)
                    elif resolved:self.unresolved.append(dict(path=child,target=resolved,reason='directory alias recorded; no forest traversal'))
                else:self.add(child,recurse=True)

    def catalog(self):
        return dict(entries=self.rows,roots=sorted(self.files),
                    bounds=dict(files=ENTRY_LIMIT,bytes=BYTE_LIMIT,seconds=115),
                    rationale='fixed source/native/runtime role roots only;32768 components,256MiB/file,2GiB stat total; no historical MIR forest')

    def snapshot(self):
        reader=Reader(self.catalog());reader.deadline=self.deadline
        pins={path:reader.pin(path) for path in sorted(self.files)}
        # Recheck ALL components/links, including ancestor-only rows. Reader's
        # stamp checks bind inode/metadata/chains, not just content equality.
        for path in sorted(self.rows):
            # Metadata-only unsafe/unknown rows remain DATA, never hashed or
            # certified by Reader. resolve rechecks every retained stamp/target.
            self.resolve(path)
        return dict(catalog=json.loads(json.dumps(self.catalog())),pins=pins)


def mapped_paths():
    with open('/proc/self/maps') as f:raw=f.read(MAPS_LIMIT+1)
    if len(raw)>MAPS_LIMIT:raise CatalogError('maps1MiB bound')
    paths=set()
    for line in raw.splitlines():
        fields=line.split(None,5)
        if len(fields)==6 and fields[5].startswith('/'):
            if fields[5].endswith(' (deleted)'):raise CatalogError('deleted mapping')
            paths.add(fields[5])
    return raw,sorted(paths)


def runtime_proposal():
    raw,mapped=mapped_paths()
    exe=sys.executable;stdlib=sysconfig.get_path('stdlib')
    if not admit(exe) or not admit(stdlib):raise CatalogError('Python role outside fixed root admission')
    return dict(executable=exe,stdlib=stdlib,mapped_libraries=mapped,maps=raw,
                mapped_file_rows=[line for line in raw.splitlines() if len(line.split(None,5))==6 and line.split(None,5)[5].startswith('/')],
                role='candidate observed runtime under existing Python/OS trust boundary; no executed-bytecode proof')


def verify_expected(snapshot,expected):
    for path,value in expected.items():
        if path not in snapshot['pins'] or snapshot['pins'][path]['sha256']!=value:
            raise CatalogError('fixed source hash drift: '+path)


def bootstrap(stage):
    """Independent transfer manifest; seal pins manifest, neither hashes itself."""
    from FinalNativeGate_bootstrap_seal import BOOTSTRAP_SHA256
    path=stage/'FinalNativeGate-bootstrap.json'
    with path.open('rb') as f:
        s=os.fstat(f.fileno())
        if s.st_size>2**20:raise CatalogError('bootstrap stat1MiB bound')
        raw=f.read(2**20+1)
        if stamp(os.fstat(f.fileno()))!=stamp(s):raise CatalogError('bootstrap manifest changed')
    if hashlib.sha256(raw).hexdigest()!=BOOTSTRAP_SHA256:raise CatalogError('bootstrap transfer seal drift')
    expected_seal='BOOTSTRAP_SHA256 = '+repr(BOOTSTRAP_SHA256)+'\n'
    seal_path=stage/'FinalNativeGate_bootstrap_seal.py'
    with seal_path.open('rb') as f:
        if os.fstat(f.fileno()).st_size!=len(expected_seal):raise CatalogError('bootstrap root seal size')
        if f.read(len(expected_seal)+1)!=expected_seal.encode():raise CatalogError('bootstrap root seal source')
    rows=json.loads(raw)
    # Independent finite source bootstrap only: no candidate Acquisition,
    # runtime/native/cache discovery, aliases or directory recursion.
    if not isinstance(rows,dict) or len(rows)>128:raise CatalogError('bootstrap finite128 files')
    rows=dict(rows)
    rows[path.name]=dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
    rows[seal_path.name]=dict(size=len(expected_seal),sha256=hashlib.sha256(expected_seal.encode()).hexdigest())
    snapshots={};total=0;deadline=time.monotonic()+115
    for name,pin in sorted(rows.items()):
        if Path(name).name!=name or name in ('.','..'):raise CatalogError('bootstrap basename required')
        if type(pin['size']) is not int or not 0<=pin['size']<=4*2**20:raise CatalogError('bootstrap file4MiB bound')
        total+=pin['size']
        if total>16*2**20:raise CatalogError('bootstrap total16MiB bound')
        held=[];chain=[]
        try:
            fd=os.open('/',os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW);held.append(fd)
            for part in (*stage.parts[1:],name):
                if time.monotonic()>deadline:raise CatalogError('bootstrap deadline')
                before=os.stat(part,dir_fd=fd,follow_symlinks=False)
                directory=part!=name
                if not (stat.S_ISDIR(before.st_mode) if directory else stat.S_ISREG(before.st_mode)) or before.st_mode&0o022:
                    raise CatalogError('bootstrap type/permissions/alias')
                sub=os.open(part,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK|(os.O_DIRECTORY if directory else 0),dir_fd=fd)
                held.append(sub)
                if stamp(os.fstat(sub))!=stamp(before):raise CatalogError('bootstrap open race')
                chain.append((sub,stamp(before)));fd=sub
            if before.st_size!=pin['size'] or before.st_nlink!=1:raise CatalogError('bootstrap size/single-link')
            h=hashlib.sha256();left=pin['size']
            while left:
                if time.monotonic()>deadline:raise CatalogError('bootstrap deadline')
                piece=os.read(fd,min(left,65536))
                if not piece:raise CatalogError('bootstrap short read')
                left-=len(piece);h.update(piece)
            if os.read(fd,1) or h.hexdigest()!=pin['sha256']:raise CatalogError('bootstrap source hash drift: '+name)
            for opened,before_stamp in chain:
                if stamp(os.fstat(opened))!=before_stamp:raise CatalogError('bootstrap source chain drift')
            snapshots[name]=dict(pin=pin,chain=[list(v) for _,v in chain])
        finally:
            for opened in reversed(held):os.close(opened)
    return dict(manifest=hashlib.sha256(raw).hexdigest(),snapshot=snapshots)


def stable(before,after):
    if before!=after:raise CatalogError('full-interval observed snapshot drift (bootstrap or acquired metadata/hash interval)')


def data_status(unresolved,errors):
    if errors:return 'COLLECTION_FAILED'
    return 'DATA_WITH_UNRESOLVED_ROLES' if unresolved else 'DATA_PENDING_LEAD_REVIEW'
