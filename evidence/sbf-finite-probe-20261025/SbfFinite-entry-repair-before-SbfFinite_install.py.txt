if __name__ == '__main__':
    raise SystemExit('SbfFinite SOURCE ONLY: installation disabled before imports')
"""Exclusive-copy source implementation, UNEXECUTED. No usable install CLI.

The bootstrap interpreter and installer bytes must be verified externally by a
separate lead-reviewed administrative procedure. No self-hash can establish that
bootstrap. Source-owned historical inputs are never adopted as destinations.
"""
import hashlib
import os
import stat
import time
from SbfFiniteLinux_capture import require, identity, canonical, DIR_FLAGS, FILE_FLAGS
from SbfFinite_fixed import CATALOG, OWN, ROOT, PACKAGE

WRITE = os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW|os.O_CLOEXEC
DEADLINE = 110

def ident(s): return list(identity(s))

def stable(s):
    # Directory timestamps may change only for directories WE create. Source
    # snapshots below compare full captured identity, including ns timestamps.
    return ident(s)

class Source:
    """Retained complete component/alias chains; never follows source links.

    Alias expansion is validated from the pinned chain, with restart at /.
    Canonical endpoint is opened component by component. All ancestors/aliases
    remain checked before AND after copy; content hash is checked separately.
    Captured inode numbers are historical and may deny a future changed host.
    """
    def __init__(self, row, api=os):
        self.api=api; self.handles=[]; self.links=[]; self.fd=None
        try:
            path=row['path']; canonical(path)
            expected=path; parent=None; prefix=None; seen=set()
            chain=row['chain']
            require(0 < len(chain) <= 256, 'source chain bound')
            for i, item in enumerate(chain):
                p=item['path']; wanted=item['identity']
                require(len(wanted)==9, 'source identity fields')
                if p=='/':
                    require(i==0 or 'target' in chain[i-1], 'unadmitted chain restart')
                    fd=api.open('/',DIR_FLAGS)
                    require(stat.S_ISDIR(wanted[2]), 'source root type')
                    self.handles.append((fd,None,None,wanted));parent=fd;prefix='/'
                else:
                    require(parent is not None and p.rsplit('/',1)[0]==prefix.rstrip('/'), 'missing direct component')
                    name=canonical(p)[-1]
                    s=api.stat(name,dir_fd=parent,follow_symlinks=False)
                    require(ident(s)==wanted, 'captured source component drift')
                    if 'target' in item:
                        require(stat.S_ISLNK(s.st_mode) and s.st_nlink==1, 'source alias type')
                        target=api.readlink(name,dir_fd=parent)
                        require(target==item['target'], 'unadmitted source alias')
                        require(expected==p or expected.startswith(p+'/'), 'alias off requested chain')
                        require(p not in seen, 'source alias cycle');seen.add(p)
                        suffix=expected[len(p):]
                        # Only source-pinned expansion is normalized; no runtime
                        # target can choose a destination or read path.
                        expected=os.path.normpath((target if target.startswith('/') else prefix.rstrip('/')+'/'+target)+suffix)
                        canonical(expected)
                        require(i+1<len(chain) and chain[i+1]['path']=='/', 'alias restart missing')
                        self.links.append((parent,name,wanted,target))
                        parent=None;prefix=None
                        continue
                    last=i==len(chain)-1
                    require(stat.S_ISREG(s.st_mode) if last else stat.S_ISDIR(s.st_mode), 'source component type')
                    fd=api.open(name, FILE_FLAGS if last else DIR_FLAGS,dir_fd=parent)
                    self.handles.append((fd,parent,name,wanted))
                    parent=fd;prefix=p
                require(ident(api.fstat(fd))==wanted, 'source opened FD drift')
            require(expected==row['physical']==chain[-1]['path'], 'source physical resolution')
            require(stat.S_ISREG(api.fstat(fd).st_mode) and api.fstat(fd).st_nlink==1, 'source final regular nlink1')
            require(api.fstat(fd).st_size==row['size'], 'source exact size')
            self.fd=fd
            self.audit()
        except BaseException:
            self.close(); raise

    def read(self,size): return self.api.read(self.fd,size)

    def audit(self):
        for fd,parent,name,wanted in self.handles:
            require(ident(self.api.fstat(fd))==wanted, 'source FD changed')
            if parent is not None:
                require(ident(self.api.stat(name,dir_fd=parent,follow_symlinks=False))==wanted, 'source entry changed')
        for parent,name,wanted,target in self.links:
            require(ident(self.api.stat(name,dir_fd=parent,follow_symlinks=False))==wanted and
                    self.api.readlink(name,dir_fd=parent)==target, 'source alias changed')

    def close(self):
        for fd,_,_,_ in reversed(self.handles): self.api.close(fd)
        self.handles=[];self.fd=None

class LiteralSource:
    """Source-pinned package bytes inside externally reviewed bootstrap bundle."""
    fd=None
    def __init__(self, raw, pin):
        self.raw=raw;self.pin=pin;self.offset=0;self.audit()
    def audit(self):
        require(len(self.raw)==self.pin['size'] and hashlib.sha256(self.raw).hexdigest()==self.pin['sha256'], 'literal package pin')
    def read(self,size):
        b=self.raw[self.offset:self.offset+size];self.offset+=len(b);return b
    def close(self): pass

class Tree:
    """One fresh destination tree. All writers close before ANY sealing.

    Readback opens fresh nofollow readers after writer close; seal opens readers
    only. Root adversary/kernel/fs semantics remain trust boundaries.
    """
    def __init__(self, rootfd, api=os, clock=time):
        self.api=api;self.clock=clock;self.started=clock.monotonic()
        self.dirs={'/':api.dup(rootfd)};self.files={};self.total=0;self.writers=set()
        self.inodes=set();self.sealed=False
        self.directory(self.dirs['/'],0o700)

    def deadline(self): require(self.clock.monotonic()-self.started<DEADLINE, 'copy deadline')

    def directory(self,fd,mode):
        s=self.api.fstat(fd)
        require(stat.S_ISDIR(s.st_mode) and s.st_uid==s.st_gid==0 and stat.S_IMODE(s.st_mode)==mode, 'destination directory rights')

    def parent(self,path):
        fd=self.dirs['/'];prefix=''
        for name in canonical(path)[:-1]:
            prefix+='/'+name
            if prefix not in self.dirs:
                self.api.mkdir(name,0o700,dir_fd=fd)
                child=self.api.open(name,DIR_FLAGS,dir_fd=fd)
                self.dirs[prefix]=child;self.directory(child,0o700)
            child=self.dirs[prefix]
            require(ident(self.api.stat(name,dir_fd=fd,follow_symlinks=False))==ident(self.api.fstat(child)), 'destination directory entry drift')
            fd=child
        return fd,canonical(path)[-1]

    def checkfile(self,fd,mode,size):
        s=self.api.fstat(fd)
        require(stat.S_ISREG(s.st_mode) and s.st_uid==s.st_gid==0 and s.st_nlink==1 and
                stat.S_IMODE(s.st_mode)==mode and s.st_size==size, 'destination regular rights/length')
        return s

    def hashread(self,fd,size):
        h=hashlib.sha256();n=0
        while True:
            self.deadline();b=self.api.read(fd,min(65536,size-n+1))
            if not b:break
            n+=len(b);require(n<=size, 'readback growth');h.update(b)
        require(n==size, 'readback size');return h.hexdigest()

    def copy(self,source,path,pin):
        self.deadline()
        require(not self.sealed and path not in self.files, 'duplicate/sealed destination')
        canonical(path)
        require(type(pin['size']) is int and 0<=pin['size']<=16*2**20 and pin['mode'] in (0o444,0o555), 'copy bounds/mode')
        require(len(self.files)<256 and self.total+pin['size']<=64*2**20, 'total copy bound')
        parent,name=self.parent(path);fd=None
        try:
            fd=self.api.open(name,WRITE,0o600,dir_fd=parent);self.writers.add(fd)
            d=self.checkfile(fd,0o600,0)
            key=(d.st_dev,d.st_ino)
            require(key not in self.inodes and (source.fd is None or key!=(self.api.fstat(source.fd).st_dev,self.api.fstat(source.fd).st_ino)), 'destination aliases another inode')
            self.inodes.add(key)
            source.audit();h=hashlib.sha256();n=0
            while True:
                self.deadline();b=source.read(min(65536,pin['size']-n+1))
                if not b:break
                n+=len(b);require(n<=pin['size'], 'source growth');h.update(b)
                offset=0
                while offset<len(b):
                    self.deadline();k=self.api.write(fd,b[offset:]);require(0<k<=len(b)-offset, 'short/invalid destination write');offset+=k
            source.audit()
            require(n==pin['size'] and h.hexdigest()==pin['sha256'], 'source bytes mismatch')
            self.api.fsync(fd);self.checkfile(fd,0o600,n)
            self.api.close(fd);self.writers.remove(fd);fd=None
            reader=self.api.open(name,FILE_FLAGS,dir_fd=parent)
            try:
                s=self.checkfile(reader,0o600,n)
                require((s.st_dev,s.st_ino)==key and self.hashread(reader,n)==pin['sha256'], 'closed-writer readback')
                require(ident(s)==ident(self.api.fstat(reader)), 'readback drift')
                self.files[path]=dict(pin=dict(pin),identity=ident(s),inode=key)
                self.total+=n
            finally:self.api.close(reader)
        finally:
            if fd is not None:self.api.close(fd);self.writers.remove(fd)

    def seal(self):
        require(not self.sealed and not self.writers, 'all writers must close before seal')
        expected={p:set() for p in self.dirs}
        for path in list(self.dirs)+list(self.files):
            if path=='/':continue
            parent,name=path.rsplit('/',1);expected[parent or '/'].add(name)
        for path,fd in self.dirs.items():
            require(set(self.api.listdir(fd))==expected[path], 'unknown/missing setup entry')
        for path,row in self.files.items():
            self.deadline();parent,name=self.parent(path)
            fd=self.api.open(name,FILE_FLAGS,dir_fd=parent)
            try:
                require(ident(self.api.fstat(fd))==row['identity'], 'preseal file drift')
                require(self.hashread(fd,row['pin']['size'])==row['pin']['sha256'], 'preseal digest')
                require(ident(self.api.fstat(fd))==row['identity'], 'seal hash drift')
                self.api.fchmod(fd,row['pin']['mode'])
                self.checkfile(fd,row['pin']['mode'],row['pin']['size'])
            finally:self.api.close(fd)
        for path,fd in sorted(self.dirs.items(),key=lambda x:-len(x[0])):
            self.directory(fd,0o700);self.api.fchmod(fd,0o555);self.api.fsync(fd)
        self.sealed=True

    def close(self):
        for fd in self.writers:self.api.close(fd)
        self.writers.clear()
        for fd in reversed(list(self.dirs.values())):self.api.close(fd)
        self.dirs.clear()


def safe_parent(path):
    """Literal destination ancestry only. Refuse root symlinks and gid drift."""
    fd=os.open('/',DIR_FLAGS)
    try:
        for name in ['']+canonical(path):
            if name:
                child=os.open(name,DIR_FLAGS,dir_fd=fd);os.close(fd);fd=child
            s=os.fstat(fd)
            require(stat.S_ISDIR(s.st_mode) and s.st_uid==s.st_gid==0 and not s.st_mode&0o022, 'root nonwritable ancestry')
        return fd
    except BaseException:os.close(fd);raise


def fresh(parent,name):
    os.mkdir(name,0o700,dir_fd=parent)
    fd=os.open(name,DIR_FLAGS,dir_fd=parent)
    try:
        s=os.fstat(fd)
        require(stat.S_ISDIR(s.st_mode) and s.st_uid==s.st_gid==0 and stat.S_IMODE(s.st_mode)==0o700,'fresh directory rights')
        return fd
    except BaseException:
        os.close(fd);raise


def fixed_install():
    """Noarguments. No path/manifest/report/GO supplied by caller. Never called.

    Inventory is source-pinned; package payload catalog is literal generated
    source. Both fresh top directories retained even on any partial failure.
    """
    require(os.getresuid()==os.getresgid()==(0,0,0),'root installer IDs')
    from SbfFinite_continue import host_stdio
    host_stdio()
    from SbfFinite_backend_candidate import status
    require(status()['Threads']=='1','single threaded installer')
    from SbfFinite_inventory import PACKAGE_CATALOG
    from SbfFinite_validate import validate_fixed
    validate_fixed()
    require(len(CATALOG)+len(PACKAGE_CATALOG)<=256 and
            35655597+sum(r['pin']['size'] for r in PACKAGE_CATALOG)<=64*2**20,
            'global setup copy count/byte bound including package')
    # Precheck BOTH absent, without following any entry; mkdir remains exclusive.
    parents=[];fds=[];trees=[]
    try:
        for p,name in (('/var/lib','SbfFinite-20261025-v1'),('/opt/aspis','SbfFinite-20261025-v1')):
            fd=safe_parent(p);parents.append(fd)
            try:os.stat(name,dir_fd=fd,follow_symlinks=False)
            except FileNotFoundError:pass
            else:raise RuntimeError('fresh setup root already exists; retain and request new reviewed root')
        own=fresh(parents[0],'SbfFinite-20261025-v1');fds.append(own)
        root=fresh(own,'rootfs');fds.append(root)
        public=fresh(own,'public-output');fds.append(public)
        journal=fresh(own,'journal-root');fds.append(journal)
        package=fresh(parents[1],'SbfFinite-20261025-v1');fds.append(package)
        tree=Tree(root);pkg=Tree(package);trees.extend((tree,pkg))
        # Empty mount targets; no placeholder payload entries.
        for target in ('tmp','proc','dev'):tree.parent('/'+target+'/.anchor')
        for row in CATALOG:
            source=Source(row['source'])
            try:tree.copy(source,row['guest'],dict(size=row['source']['size'],sha256=row['source']['sha256'],mode=row['mode']))
            finally:source.close()
        require(len(tree.files)==92 and tree.total==35655597,'exact finite copy accounting')
        for row in PACKAGE_CATALOG:
            source=LiteralSource(row['payload'],row['pin'])
            try:pkg.copy(source,'/'+row['name'],row['pin'])
            finally:source.close()
        require(not tree.writers and not pkg.writers,'all setup writers closed')
        tree.seal();pkg.seal()
        return dict(status='copied and sealed finite input; not an execution observation',rows=92,bytes=35655597)
    finally:
        for tree in reversed(trees):tree.close()
        for fd in reversed(fds+parents):os.close(fd)
